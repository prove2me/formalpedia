-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
-- name    : LanglandsTunnell.CubicInduction.le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/5471c91d-2edd-5ff8-bf28-e086ea350e8d
-- title:
--   At most one unipotent-invariant functional on each corner-filtration step
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$) and a triple $\chi = (\chi_0,\chi_1,\chi_2)$ of multiplicative characters of the units of the $v$-adic completion $\mathbb{Q}_v$ with values in $\mathbb{C}^\times$; write $G = \mathrm{GL}_3(\mathbb{Q}_v)$ and let $\mathrm{principalSeries3}\,v\,\chi$ be the space of locally constant $f : G \to \mathbb{C}$ that are left invariant under the upper unipotent matrices $\mathrm{upperUnipotent3}\,x\,y\,z$ and satisfy $f(\mathrm{diag}(a)g) = \big(\prod_i \chi_i(a_i)\big)\,(\lVert a_0\rVert/\lVert a_2\rVert)\,f(g)$. Let $Z : \mathrm{Fin}\,7 \to$ subsets of $G$ be the chain given entrywise by $\emptyset$; $\{g_{20}=g_{10}=g_{21}=0\}$; $\{g_{20}=g_{21}=0\}$; $\{g_{20}=0,\ g_{10}g_{21}=0\}$; $\{g_{20}=0\}$; $\{g_{20}\,(g_{10}g_{21}-g_{11}g_{20})=0\}$; all of $G$, and let $W\,k$ be the subspace of sections of the principal series vanishing at every point of $Z\,k$ (the intersection of the kernels of the evaluation maps at $g \in Z\,k$, pulled back along the inclusion). Let $i \in \mathrm{Fin}\,6$, $n \in \mathbb{N}$ and $\Lambda_0,\dots,\Lambda_{n-1}$ be $\mathbb{C}$-linear functionals on the principal series. If each $\Lambda_j$ is invariant under right translation by all upper unipotent matrices, each $\Lambda_j$ vanishes on $W\,(i+1)$, and the restrictions of the $\Lambda_j$ to $W\,i$ are linearly independent over $\mathbb{C}$, then $n \le 1$.
--
--   This is the one-dimensionality of unipotent coinvariants on each graded piece of the filtration of a principal series of $\mathrm{GL}_3(\mathbb{Q}_v)$ by the closed unions of Bruhat cells cut out by the bottom-left entry, its two neighbours and the bottom-left $2\times 2$ minor, stated as a bound on the size of a linearly independent family of functionals. It feeds the counting statement [`LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3`](thm.html#LanglandsTunnell.CubicInduction.card_le_ncard_of_linearIndependent_of_upperUnipotent3_of_diagonal3), which bounds the dimension of Whittaker-type functionals on the principal series.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_le_one_of_linearIndependent_domRestrict_of_upperUnipotent3.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem
    LanglandsTunnell.CubicInduction.le_one_of_linearIndependent_domRestrict_of_upperUnipotent3
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ))
    (Z : Fin 7 → Set (LocalGL3 v))
    (hZ : Z = ![∅,
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0 ∧ gl3Entry v g 1 0 * gl3Entry v g 2 1 = 0},
      {g | cornerEntry v g = 0},
      {g | cornerEntry v g * lowerMinor v g = 0},
      Set.univ])
    (W : Fin 7 → Submodule ℂ ↥(principalSeries3 v χ))
    (hW : ∀ k : Fin 7, W k = Submodule.comap (principalSeries3 v χ).subtype
      (⨅ g ∈ Z k, LinearMap.ker (LinearMap.proj g : (LocalGL3 v → ℂ) →ₗ[ℂ] ℂ)))
    (i : Fin 6) (n : ℕ)
    (Λ : Fin n → (↥(principalSeries3 v χ) →ₗ[ℂ] ℂ)) :
    (∀ j, ∀ (x y z : v.adicCompletion ℚ) (f : ↥(principalSeries3 v χ)),
      Λ j ⟨gl3AmbientRightTranslate (R := ℂ) (upperUnipotent3 x y z) f,
          rightTranslate_mem_principalSeries3 f.2 (upperUnipotent3 x y z)⟩ = Λ j f) →
    (∀ j, ∀ f ∈ W i.succ, Λ j f = 0) →
    LinearIndependent ℂ (fun j => (Λ j).domRestrict (W i.castSucc)) →
    n ≤ 1 := by sorry
