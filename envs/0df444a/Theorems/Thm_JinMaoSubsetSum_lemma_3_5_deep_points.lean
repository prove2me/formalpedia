-- Prove2me | Theorems.Thm_JinMaoSubsetSum_lemma_3_5_deep_points
-- name    : JinMaoSubsetSum.lemma_3_5_deep_points
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T10:40:11.883735+00:00
-- url     : https://prove2.me/theorems/49f2363c-30ba-4aa5-8969-2f5b4d138f64
-- title:
--   Lemma 3.5 — deep lattice points of $Z(X)$ are subset sums: $(Z(X)\ominus|X'|H)\cap\Gamma\subseteq\Sigma(X)$
-- statement:
--   **Lemma 3.5.** Let $H\cap\Gamma$ be a progression of rank $d\ge1$ (Definition 3.3 with $f$ the identity), and let $X$ be a multiset with $\operatorname{supp}(X)\subseteq H\cap\Gamma$. If a sub-multiset $X'\subseteq X$ is $d$-generating for $H\cap\Gamma$, then
--   $$
--   \bigl(Z(X)\ominus|X'|H\bigr)\cap\Gamma\subseteq\Sigma(X).
--   $$
--
--   Every lattice point lying deep inside the zonotope of $X$, at depth $|X'|H$, is a subset sum of $X$. This is the structural fact behind the algorithm: only the subset sums in a thin shell near the boundary of the zonotope remain to be computed.
--
--   **Formalization Note** The ambient space is $\mathbb R^m$ (`Fin m → ℝ`) with $\Gamma$ of rank $d$; $|X'|$ counts multiplicity and $|X'|H$ is the dilation.
--
--   Differences from the source:
--   - encoding: the ambient space of the progression (the proof assumes it is ℝ^d without loss of generality) → ambient ℝ^m (Fin m → ℝ), Γ a discrete subgroup of rank d, H ⊆ span Γ; reason: Definition 3.3 leaves the ambient space free; this is the same statement
-- source:
--   Jin, Mao, Subset Sum in Almost-Linear Time, arXiv:2610.20742v1 (sha256 8b604948862d9188e922b8abf95831fde3a3699e26d39177d20a1460e31a926a), Lemma 3.5, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_JinMaoSubsetSum_subsetSums
import Definitions.Def_JinMaoSubsetSum_zonotope
import Definitions.Def_JinMaoSubsetSum_IsProgression

set_option autoImplicit false

open scoped Pointwise

namespace JinMaoSubsetSum

/-- **Lemma 3.5** (Jin, Mao, *Subset Sum in Almost-Linear Time*, arXiv:2610.20742v1, p.17): "Let
H ∩ Γ be a progression of rank d ≥ 1, and let X be a multiset with supp(X) ⊆ H ∩ Γ. If a
submultiset X′ ⊆ X is d-generating for H ∩ Γ, then (Z(X) ⊖ |X′|H) ∩ Γ ⊆ Σ(X)."

**Formalization Note.** The ambient space is `ℝ^m`; "H ∩ Γ is a progression of rank d" is
Definition 3.3 with `f` the identity (`IsProgression Γ H d`: `Γ` discrete of rank `d`, `H ⊆ span Γ`
origin-symmetric compact convex, `dim span(H ∩ Γ) = d`), which is automatically proper.
`Z(X)` is the zonotope of the multiset (with multiplicity), `⊖` the erosion, `|X′|` the size of
`X′` and `|X′|H` the dilation. -/
theorem lemma_3_5_deep_points {m d : ℕ} (hd : 1 ≤ d) (Γ : AddSubgroup (Fin m → ℝ))
    (H : Set (Fin m → ℝ)) (hprog : IsProgression Γ H d) (X X' : Multiset (Fin m → ℝ))
    (hX : ∀ x ∈ X, x ∈ H ∧ x ∈ Γ) (hX'X : X' ≤ X) (hgen : IsSGenerating H Γ (d : ℝ) X') :
    erosion (zonotope X) ((Multiset.card X' : ℝ) • H) ∩ (Γ : Set (Fin m → ℝ)) ⊆
      subsetSums X := by sorry

end JinMaoSubsetSum
