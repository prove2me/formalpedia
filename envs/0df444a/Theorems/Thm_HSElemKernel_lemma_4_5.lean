-- Prove2me | Theorems.Thm_HSElemKernel_lemma_4_5
-- name    : HSElemKernel.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T17:28:40.340091+00:00
-- url     : https://prove2.me/theorems/68d541cf-9cd6-46fe-84dc-19efbd60ab39
-- title:
--   Lemma 4.5 — $N = O_d(k + Btq_2L)$ and $M = O_d(mt^{d-1}L^{d-1} + N)$ for $\Phi_{\mathcal F}$
-- statement:
--   Let $d \ge 3$ and let $E$ be a cardinality encoder meeting Lemma 3.2's guarantee with constant $C_E$. Let $(U, \mathcal S, k)$ be an instance of $d$-Hitting Set preprocessed as in Section 2.1 ($\emptyset \notin \mathcal S$, $\mathcal S \ne \emptyset$, $2 \le k < |U|$), and $X \subseteq U$ with $|X| \le dk$ and $|A \cap W| \le d - 1$ for all $A \in \mathcal S$, $W = U \setminus X$ (Section 2.2). Let $\mathcal F$ be a two-level hash pair with $t, q_2 \ge 1$ and $\gamma : U \to \{0,1\}^\ell$. Write $m = |\mathcal S|$, $L = 1 + \ell$, and $N$, $M$ for the numbers of variables and clauses of $\Phi_{\mathcal F}$. Then
--   $$N = O_d(k + Btq_2L), \qquad M = O_d\big(mt^{d-1}L^{d-1} + N\big). \tag{12}$$
--
--   Precisely: for every $d \ge 3$ and $C_E$ there is $C > 0$ such that, for all such $E$, instances, $X$, $\mathcal F$, $\ell$ and $\gamma$,
--   $$N \le C\,(k + Btq_2(1 + \ell)), \qquad M \le C\,\big(m\,t^{d-1}(1+\ell)^{d-1} + N\big).$$
--
--   Substituting the parameters of Lemma 4.2 gives the size bounds of Lemma 2.2.
--
--   **Formalization Note** $N$ is the number of elements of the variable set of $\Phi_{\mathcal F}$ (Table 2 plus the auxiliary variables of the cardinality encodings and of (7), (8)), $M$ the number of listed clauses.
--
--   Differences from the source:
--   - reading: Lemma 4.5 for the preprocessed instance of Section 2.1 and the X of Section 2.2 → hypotheses ∅ ∉ S, S ≠ ∅, 2 ≤ k < n, |X| ≤ dk and |A \ X| ≤ d − 1 for all A ∈ S; reason: the context of Lemma 4.5: Section 2.1's standing assumptions and the two properties of X the proof uses (|X| = O_d(k) and (11))
--   - reading: F sampled by Lemma 4.2 → hypotheses t ≥ 1 and q₂ ≥ 1; reason: the sampled F has t = ⌈log₈(8B)⌉ ≥ 1 and q₂ = 4b² ≥ 1 (p.10); without them N is not O(k + Btq₂L), since the B encodings of (5) need auxiliaries even at t = 0
--   - generalization: X from a maximal packing, F sampled by Lemma 4.2, ℓ = ⌈log₂(|W|+1)⌉, the encoder of Lemma 3.2 → any X, F, ℓ, γ and encoder satisfying the hypotheses above; reason: the bounds hold for all of them; they specialize to the paper's Φ_F
--   - encoding: O_d(·) → explicit C chosen after d and the encoder constant C_E, before the instance; reason: O_d hides constants depending on d (and on the fixed encoder of Lemma 3.2)
-- source:
--   Sheng–Xiao, A Near-Linear Element-Kernel for d-Hitting Set, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.5, Eq. (12), p.13

import Mathlib
import Definitions.Def_HSElemKernel_IsDHS
import Definitions.Def_HSElemKernel_phiF

namespace HSElemKernel

/-- **Lemma 4.5** (Sheng–Xiao, *A Near-Linear Element-Kernel for d-Hitting Set*, arXiv:2609.06512 (held version, sha256 aca9c70e…), Lemma 4.5, p.13, Eq. (12)): the numbers `N` of variables and `M` of
clauses of `Φ_F` satisfy
$$N = O_d(k + Btq₂L), \qquad M = O_d(m t^{d−1} L^{d−1} + N),$$
with `m = |S|` and `L = 1 + ℓ`.

For `d ≥ 3` and an encoder constant `C_E` there is `C` such that for every encoder `E` with
Lemma 3.2's guarantee (constant `C_E`), every `d`-Hitting Set instance preprocessed as in
Section 2.1 (`∅ ∉ S`, `S ≠ ∅`, `2 ≤ k < n`), every `X` with `|X| ≤ dk` and
`|A ∩ W| ≤ d − 1` for all `A ∈ S` (Section 2.2), every pair `F` with `t, q₂ ≥ 1` and every
address map `γ : U → {0,1}^ℓ`: `N ≤ C(k + Btq₂(1 + ℓ))` and
`M ≤ C(m t^{d−1}(1 + ℓ)^{d−1} + N)`.

**Formalization Note** `N` is `Fintype.card` of the variable type, `M` the number of clauses.
`t, q₂ ≥ 1` hold for the sampled `F` of Lemma 4.2 (`t = ⌈log₈(8B)⌉`, `q₂ = 4b²`, p.10); the
bound holds for every `ℓ` and every `γ`, in particular `ℓ = ⌈log₂(|W| + 1)⌉`. -/
theorem lemma_4_5 (d : ℕ) (hd : 3 ≤ d) (CE : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ E : CardEncoder, E.Spec CE →
      ∀ I : HSInstance, IsDHS d I → ∅ ∉ I.S → I.S.Nonempty → 2 ≤ I.k → I.k < I.n →
      ∀ X : Finset (Fin I.n), X.card ≤ d * I.k → (∀ A ∈ I.S, (A \ X).card ≤ d - 1) →
      ∀ F : TwoLevelHash (Fin I.n), 1 ≤ F.t → 1 ≤ F.q2 →
      ∀ (ℓ : ℕ) (γ : Fin I.n → Fin ℓ → Bool),
        (Fintype.card (PhiVar E X F ℓ I.k) : ℝ) ≤
            C * ((I.k : ℝ) + F.B * F.t * F.q2 * (1 + (ℓ : ℝ))) ∧
          ((phiF E I.S I.k X F γ).length : ℝ) ≤
            C * ((I.S.card : ℝ) * (F.t : ℝ) ^ (d - 1) * (1 + (ℓ : ℝ)) ^ (d - 1) +
              Fintype.card (PhiVar E X F ℓ I.k)) := by sorry

end HSElemKernel
