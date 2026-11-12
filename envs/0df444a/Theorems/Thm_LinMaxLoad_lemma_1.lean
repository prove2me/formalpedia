-- Prove2me | Theorems.Thm_LinMaxLoad_lemma_1
-- name    : LinMaxLoad.lemma_1
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T16:35:35.952361+00:00
-- url     : https://prove2.me/theorems/b052bde8-b731-4f4b-abdd-6df23a8d6e3b
-- title:
--   Lemma 1 — $\Pr_h[\forall i,\ h(s_i)=y_i] \le q^{-\ell\cdot\dim\langle s_1,\dots,s_k\rangle}$
-- statement:
--   Let $K$ be a finite field with $q$ elements, $E$ a finite $K$-vector space, and $h : E \to K^\ell$ a uniformly random linear map. For any $s_1, \dots, s_k \in E$ and $y_1, \dots, y_k \in K^\ell$,
--
--   $$
--   \Pr_h\big[\forall i,\ h(s_i) = y_i\big] \le q^{-\ell \cdot \dim \langle s_1, \dots, s_k \rangle},
--   $$
--
--   where $\langle s_1,\dots,s_k\rangle$ is the span. Moreover, equality holds when $y_1 = \dots = y_k = 0$.
--
--   This is the basic fact about random linear maps that the paper cites from [ABF23, Lemma 4.8]; its case $k = 1$ gives $\Pr[h(v) = 0] = q^{-\ell}$ for $v \ne 0$, which the proof of Lemma 7 uses.
--
--   Differences from the source:
--   - generalization: $\mathbb F_p^u$ and the field $\mathbb F_p$ → any finite $K$-module $E$ over any finite field $K$ ($q = |K|$); reason: the argument uses only linear algebra over a finite field; $K = \mathbb F_p$, $E = \mathbb F_p^u$ (`ZMod p`, `Fin u → ZMod p`) is the source statement
--   - encoding: $p^{-\ell \cdot \dim\langle s_1,\dots,s_k\rangle}$, indices $1,\dots,k$ → $(q^{\ell \cdot \dim})^{-1}$ with $q = |K|$, indices `Fin k`; reason: Lean convention; same values
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Lemma 1 ([ABF23, Lemma 4.8]), p.8

import Mathlib
import Definitions.Def_LinMaxLoad_probLin

namespace LinMaxLoad

/-- **Lemma 1** (\[ABF23, Lemma 4.8\]; p.8 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)).
Let `h : E → K^ℓ` be a uniformly random linear map. For any `s₁, …, s_k ∈ E` and
`y₁, …, y_k ∈ K^ℓ`, `Pr_h[∀ i, h(s_i) = y_i] ≤ q^{−ℓ · dim⟨s₁, …, s_k⟩}`, with equality when
`y₁ = ⋯ = y_k = 0`; here `q = |K|`.

**Formalization Note** The page states it for `E = F_p^u` and `K = F_p`; here `K` is any
finite field and `E` any finite `K`-module (the case `K = ZMod p`, `E = Fin u → ZMod p` is the
page's). Indices are `Fin k`. -/
theorem lemma_1 {K E : Type*} [Field K] [Fintype K] [AddCommGroup E] [Module K E] [Finite E]
    (ℓ k : ℕ) (s : Fin k → E) (y : Fin k → (Fin ℓ → K)) :
    probLin K E ℓ (fun h => ∀ i, h (s i) = y i) ≤
        ((Fintype.card K : ℝ) ^ (ℓ * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ ∧
      probLin K E ℓ (fun h => ∀ i, h (s i) = 0) =
        ((Fintype.card K : ℝ) ^ (ℓ * Module.finrank K (Submodule.span K (Set.range s))))⁻¹ := by sorry

end LinMaxLoad
