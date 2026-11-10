-- Prove2me | Theorems.Thm_MultAddExt_Multiplicative_lemma_8_1
-- name    : MultAddExt.Multiplicative.lemma_8_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:41.357179+00:00
-- url     : https://prove2.me/theorems/0e1c5710-7a6b-40a0-bd03-da5ff26f5ec3
-- title:
--   Lemma 8.1 — a small nondeterministic circuit approximately thresholds a sum of maxima of acceptance probabilities
-- statement:
--   Let $C(u,y,v,r)$ be a nondeterministic circuit with inputs of lengths $n_u,n_y,n_v,n_r$, and for $u\in\{0,1\}^{n_u}$ let
--   $$S(u)=\sum_{y\in\{0,1\}^{n_y}}\ \max_{v\in\{0,1\}^{n_v}}\ \Pr_{r\leftarrow\{0,1\}^{n_r}}\bigl[C(u,y,v,r)=1\bigr].$$
--   For every rational $0<\Theta\le 2^{n_y}$ and every $0<\eta\le 1/2$ there is a nondeterministic circuit $V(u)$ such that for every $u$,
--   $$S(u)\ge\Theta\implies V(u)=1,\qquad S(u)\le(1-\eta)\Theta\implies V(u)=0,$$
--   and the size of $V$ is polynomial in the size of $C$, the input lengths, the bit length of $\Theta$ and $1/\eta$: there are absolute constants $c_0,a_0$ with $\mathrm{size}(V)\le c_0\,(\mathrm{size}(C)+n_u+n_y+n_v+n_r+\mathrm{bits}(\Theta)+1/\eta)^{a_0}$.
--
--   It is what makes the tests of §§9–10 implementable by small nondeterministic circuits.
--
--   Differences from the source:
--   - encoding: Boolean circuits over an unspecified basis; size includes input, output and witness lengths (p. 18) → Circ: fan-in-two AND/OR and NOT gates (published QCSepTotal.Gates), with fixed Boolean constant wires; size = gates + variable inputs + outputs; NondetCirc / MultiNondetCirc use a Circ on (x, wit), counting witness bits in size; reason: a standard complete basis, including constants at zero input length; the paper fixes no basis, and changing the treatment of constant wires costs at most two gates
--   - reading: size polynomial in the size of C, the input lengths, the bit length of Θ, and 1/η → ∃ c₀ a₀ ∈ ℕ fixed before all other quantifiers, size ≤ c₀·(sum of the listed parameters)^{a₀}; reason: one absolute polynomial; the parameter sum is at least 2 because 1/η ≥ 2, so a constant term is absorbed into c₀
--   - encoding: C(u, y, v, r) with four inputs; bit length of the rational Θ → a NondetCirc on the concatenation u‖y‖v‖r; bits(Θ) = Nat.size |num Θ| + Nat.size (den Θ) in lowest terms; reason: same circuits; the bit length of a reduced fraction
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), p. 45 (PDF 49), Lemma 8.1

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-- **Lemma 8.1** (Counting a sum of maximums), p. 45. For a nondeterministic circuit
`C(u, y, v, r)` with inputs of lengths `n_u, n_y, n_v, n_r`, let
`S(u) = ∑_{y} max_{v} Pr_{r}[C(u, y, v, r) = 1]`. For every rational `0 < Θ ≤ 2^{n_y}` and
`0 < η ≤ 1/2` there is a nondeterministic circuit `V(u)` with `S(u) ≥ Θ ⟹ V(u) = 1` and
`S(u) ≤ (1 − η)Θ ⟹ V(u) = 0`, of size polynomial in the size of `C`, the input lengths, the bit
length of `Θ` and `1/η` (one polynomial `c₀ · (·)^{a₀}` for all instances). -/
theorem lemma_8_1 : ∃ c₀ a₀ : ℕ, ∀ (nu ny nv nr : ℕ) (C : NondetCirc (nu + ny + nv + nr))
    (Θ : ℚ) (η : ℝ), 0 < Θ → (Θ : ℝ) ≤ (2 : ℝ) ^ ny → 0 < η → η ≤ 1 / 2 →
    ∃ V : NondetCirc nu,
      (V.size : ℝ) ≤ c₀ * ((C.size + nu + ny + nv + nr + Θ.num.natAbs.size + Θ.den.size : ℝ)
        + 1 / η) ^ a₀ ∧
      ∀ (u : Fin nu → Bool) (S : ℝ),
        S = ∑ y : Fin ny → Bool, Finset.univ.sup' Finset.univ_nonempty (fun v : Fin nv → Bool =>
          probEvent (uniform (Fin nr → Bool))
            {r | C.accepts (Fin.append (Fin.append (Fin.append u y) v) r)}) →
        ((Θ : ℝ) ≤ S → V.accepts u) ∧ (S ≤ (1 - η) * Θ → ¬ V.accepts u) := by sorry

end MultAddExt.Multiplicative
