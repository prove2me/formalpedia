-- Prove2me | Theorems.Thm_MaskedLinx_lemma_2_3_diagonal_monotone_concave
-- name    : MaskedLinx.lemma_2_3_diagonal_monotone_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T19:41:05.355987+00:00
-- url     : https://prove2.me/theorems/f7f6f346-dd22-44db-8179-fc56297dc651
-- title:
--   Lemma 2.3 — for diagonal $C$, $f(C,s;\cdot)$ is monotone in each $x_i$ and concave on $[0,1]^n$
-- statement:
--   Let $C=\mathrm{Diag}(d)$ with $d\in\mathbb R^n$, $d_1\ge d_2\ge\dots\ge d_n>0$, and let $f(C,s;x)$ be the unscaled linx objective, considered on the box $[0,1]^n$ (for diagonal $C$ it equals $\tfrac12\log\prod_i((d_i^2-1)x_i+1)$ there). Then:
--
--   1. $f(C,s;x)$ is finite for every $x\in[0,1]^n$;
--   2. if $d_i>1$, then $f(C,s;x)$ strictly increases with $x_i\in[0,1]$, the other coordinates fixed;
--   3. if $d_i=1$, then $f(C,s;x)$ does not change with $x_i\in[0,1]$;
--   4. if $d_i<1$, then $f(C,s;x)$ strictly decreases with $x_i\in[0,1]$;
--   5. $f(C,s;\cdot)$ is concave on $[0,1]^n$;
--   6. if $d_i\ne1$ for all $i$, then $f(C,s;\cdot)$ is strictly concave on $[0,1]^n$.
--
--   This is the analytic input for the closed-form optimal solutions of (1) for diagonal $C$ (Theorem 2.8) and for the optimal scaling of diagonal matrices (Proposition 3.1).
--
--   **Formalization Note** Indices are `Fin n` and $d_1\ge\dots\ge d_n$ is `Antitone d`. Concavity is stated for the real-valued function `EReal.toReal ∘ f`, which is faithful because part 1 asserts $f$ is finite on the box.
--
--   Differences from the source:
--   - generalization: the conclusion lists monotonicity and concavity → it also asserts that f is finite on [0,1]ⁿ; reason: the first line of the paper's proof, (d²ᵢ − 1)xᵢ + 1 > 0; it makes the real-valued concavity statement faithful and only adds to the conclusion
--   - encoding: f(C,s;·) concave / strictly concave on [0,1]ⁿ → ConcaveOn / StrictConcaveOn of EReal.toReal ∘ f on Set.Icc 0 1; reason: concavity needs real values; f is finite there by the first clause
-- source:
--   Chen, Fampa, Lee, Masking Anstreicher's linx bound for improved entropy bounds, arXiv:2106.02980v1, Lemma 2.3, p.4 (formula for diagonal C, §2, p.3)

import Mathlib
import Definitions.Def_MaskedLinx_linxObjective

namespace MaskedLinx

/-- **Lemma 2.3 (monotonicity and concavity of the linx objective for diagonal `C`).**
Chen, Fampa, Lee, *Masking Anstreicher's linx bound for improved entropy bounds*,
arXiv:2106.02980v1, Lemma 2.3, p.4:
"Let C := Diag(d), where d ∈ ℝⁿ satisfies d₁ ≥ d₂ ≥ ··· ≥ dₙ > 0 and 0 ≤ x ≤ e. Then f(C,s;x)
strictly increases with xᵢ, if dᵢ > 1, does not change with xᵢ, if dᵢ = 1, and strictly decreases
with xᵢ, if dᵢ < 1. Furthermore, f(C,s;·) is concave in [0,1]ⁿ and strictly concave if dᵢ ≠ 1,
for all i ∈ N."

Here `f(C,s;x)` is the unscaled objective `linxObjective (diagonal d) s 1 x`. The conclusion has
six parts:
1. `f` is finite on the box `[0,1]ⁿ` (the first line of the paper's proof);
2. for `dᵢ > 1`, `t ↦ f(x with xᵢ := t)` is strictly increasing on `[0,1]`;
3. for `dᵢ = 1`, it is constant on `[0,1]`;
4. for `dᵢ < 1`, it is strictly decreasing on `[0,1]`;
5. `f` (as a real-valued function) is concave on `[0,1]ⁿ`;
6. if `dᵢ ≠ 1` for all `i`, it is strictly concave on `[0,1]ⁿ`.

**Formalization Note.** Indices are `Fin n` (0-based) and `d₁ ≥ ⋯ ≥ dₙ` is `Antitone d`.
Concavity is stated for `EReal.toReal ∘ f`, which is faithful because part 1 asserts that `f` is
finite on the box. -/
theorem lemma_2_3_diagonal_monotone_concave (n : ℕ) (d : Fin n → ℝ) (hd : Antitone d)
    (hpos : ∀ i, 0 < d i) (s : ℕ) :
    (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
      linxObjective (Matrix.diagonal d) s 1 x ≠ ⊥ ∧
      linxObjective (Matrix.diagonal d) s 1 x ≠ ⊤) ∧
    (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, 1 < d i →
      StrictMonoOn (fun t => linxObjective (Matrix.diagonal d) s 1 (Function.update x i t))
        (Set.Icc 0 1)) ∧
    (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, d i = 1 → ∀ t ∈ Set.Icc (0 : ℝ) 1,
      linxObjective (Matrix.diagonal d) s 1 (Function.update x i t) =
        linxObjective (Matrix.diagonal d) s 1 x) ∧
    (∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1, ∀ i, d i < 1 →
      StrictAntiOn (fun t => linxObjective (Matrix.diagonal d) s 1 (Function.update x i t))
        (Set.Icc 0 1)) ∧
    ConcaveOn ℝ (Set.Icc (0 : Fin n → ℝ) 1)
      (fun x => (linxObjective (Matrix.diagonal d) s 1 x).toReal) ∧
    ((∀ i, d i ≠ 1) → StrictConcaveOn ℝ (Set.Icc (0 : Fin n → ℝ) 1)
      (fun x => (linxObjective (Matrix.diagonal d) s 1 x).toReal)) := by sorry

end MaskedLinx
