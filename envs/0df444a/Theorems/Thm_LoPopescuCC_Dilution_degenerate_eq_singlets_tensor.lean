-- Prove2me | Theorems.Thm_LoPopescuCC_Dilution_degenerate_eq_singlets_tensor
-- name    : LoPopescuCC.Dilution.degenerate_eq_singlets_tensor
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:42:46.605284+00:00
-- url     : https://prove2.me/theorems/1c0bdbe5-9386-4e25-b145-67d0d7f00953
-- title:
--   Eq. (8) — degenerate Schmidt coefficients factor off singlets: $\Pi=\Phi^r\otimes\Gamma$
-- statement:
--   Let $v$ be a bipartite vector whose Schmidt coefficients are $2^r$-fold degenerate, and let $L$ satisfy $\operatorname{SchmidtRank}(v)\le 2^rL\le\min(|a|,|b|)$, where $|a|$, $|b|$ are the local dimensions. Then there are isometries $V_A$, $V_B$ from $\mathbb C^{2^r}\otimes\mathbb C^{L}$ into Alice's and Bob's spaces and a vector $\Gamma\in\mathbb C^L\otimes\mathbb C^L$ with
--
--   $$
--   v=(V_A\otimes V_B)\,(\Phi^{r}\otimes\Gamma),\qquad 2^r\operatorname{SchmidtRank}(\Gamma)=\operatorname{SchmidtRank}(v).
--   $$
--
--   The degeneracy of the Schmidt coefficients is thus exactly the presence of $r$ singlets up to local operations. The proof of the Theorem uses this on the dominant part $u_1$ of $\psi^N$.
--
--   **Formalization Note** The paper's setting is $a=b=\{0,1\}^n$, $L=2^{n-r}$, $r\le n$. There the isometries are square, hence unitary, and $\Gamma$ has at most $2^{n-r}$ Schmidt terms.
--
--   Differences from the source:
--   - generalization: Π a state of two 2^n-dimensional systems, 2^r-fold degenerate Schmidt coefficients, bi-local unitaries → any vector v in any finite dimensions, multiplicities divisible by 2^r, local isometries, any L with SchmidtRank v ≤ 2^r L ≤ min(|a|, |b|); reason: the proof of the Theorem (p. 5) applies Eq. (8) to the unnormalized u₁ with degeneracies that are multiples of 2^d; a = b = Qubits n, L = 2^(n−r) gives the page's claim with square, hence unitary, maps
--   - encoding: Γ's Schmidt decomposition contains only 2^(n−r) terms → Γ on Fin L × Fin L with 2^r · SchmidtRank Γ = SchmidtRank v; reason: at L = 2^(n−r) the type of Γ gives the page's bound, and the equation records the exact count
-- source:
--   Lo, Popescu, The classical communication cost of entanglement manipulation, arXiv:quant-ph/9902045v2, Eq. (8), proof of the Lemma, p. 4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_LoPopescuCC_Dilution_singletPow
import Definitions.Def_LoPopescuCC_Dilution_schmidtRank
import Definitions.Def_LoPopescuCC_Dilution_IsSchmidtDegenerate
import Definitions.Def_LoPopescuCC_Dilution_pairTensor
import Definitions.Def_LoPopescuCC_Dilution_bilocal

open scoped Matrix

namespace LoPopescuCC.Dilution

/-- **Degenerate Schmidt coefficients factor off singlets** (Lo, Popescu,
arXiv:quant-ph/9902045v2, Eq. (8), proof of the Lemma, p. 4). If the multiplicities of the Schmidt
coefficients of `v` are divisible by `2^r`, then up to local isometries `v = Φ^r ⊗ Γ`, where the
Schmidt rank of `Γ` is that of `v` divided by `2^r`. `L` is any size for the residual system with
`SchmidtRank v ≤ 2^r L ≤ min(|a|, |b|)`.

**Formalization Note** The paper's setting (each system `2^n`-dimensional, `Π` normalized, `r ≤ n`)
is the instance `a = b = Qubits n`, `L = 2^{n−r}`. There the isometries are square, hence unitary,
and `Γ` has at most `2^{n−r}` Schmidt terms. The proof of the Theorem (p. 5) applies Eq. (8) to the
unnormalized `u₁` in general dimensions, which is why `v` and the dimensions are arbitrary. -/
theorem degenerate_eq_singlets_tensor {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (r L : ℕ) (v : EuclideanSpace ℂ (a × b)) (hdeg : IsSchmidtDegenerate (2 ^ r) v) (hrank : schmidtRank v ≤ 2 ^ r * L) (hLa : 2 ^ r * L ≤ Fintype.card a) (hLb : 2 ^ r * L ≤ Fintype.card b) : ∃ (VA : Matrix a (QAlgorithms.Qubits r × Fin L) ℂ) (VB : Matrix b (QAlgorithms.Qubits r × Fin L) ℂ) (Γ : EuclideanSpace ℂ (Fin L × Fin L)), VAᴴ * VA = 1 ∧ VBᴴ * VB = 1 ∧ v = bilocal VA VB (pairTensor (singletPow r) Γ) ∧ 2 ^ r * schmidtRank Γ = schmidtRank v := by sorry

end LoPopescuCC.Dilution
