-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
-- name    : LanglandsTunnell.CubicInduction.exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/39e598fd-4003-5c6d-9ae7-3cf56fd40fbd
-- title:
--   Adelic GL₃ element supported at a single finite place
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal O_K$, let $v$ be a nonzero prime ideal of $\mathcal O_K$ (a point of the height-one spectrum), and let $y$ be an element of $\mathrm{GL}_3$ over the $v$-adic completion $K_v$ of $K$. The assertion is that there exists $k$ in $\mathrm{GL}_3$ over the adele ring of $K$ (the group `AdelicGL 3 (𝓞 K) K` of invertible $3\times 3$ matrices over `AdeleRing (𝓞 K) K`) with the following three properties. First, the image of $k$ under the map of general linear groups induced by the projection of the adele ring onto the infinite adele ring is the identity matrix. Second, the image of $k$ under the map of general linear groups induced by the ring homomorphism taking an adele to its finite part and then evaluating at $v$ is exactly $y$. Third, for every nonzero prime $w \neq v$ of $\mathcal O_K$, the corresponding $w$-component of $k$, formed by the same recipe (finite part followed by evaluation at $w$), is the identity matrix.
--
--   This is the elementary surjectivity statement for the embedding of the local group $\mathrm{GL}_3(K_v)$ into $\mathrm{GL}_3(\mathbb A_K)$ at a single finite place, reflecting the restricted-product description of the adeles: a matrix that is the identity away from $v$ is adelic. It is used to convert local translates at one place into adelic translates that are trivial elsewhere, in the zeta-integral factorisation for cubic induction data and in the Rankin–Selberg realisation arguments that cite it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_adelicGL3_archComponent3_eq_one_componentAt3_eq.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.exists_adelicGL3_archComponent3_eq_one_componentAt3_eq
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (y : GL (Fin 3) (v.adicCompletion K)) :
    ∃ k : AdelicGL 3 (𝓞 K) K,
      archComponent3 (𝓞 K) K k = 1 ∧ componentAt3 (𝓞 K) K v k = y ∧
      ∀ w : HeightOneSpectrum (𝓞 K), w ≠ v → componentAt3 (𝓞 K) K w k = 1 := by sorry
