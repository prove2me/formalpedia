-- Prove2me | Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq
-- name    : MvPolynomial.CrossingQuotient.Resolution.mem_support_iff_eq_addVal_of_comp_toCrossing_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/6237de11-b84d-5d35-8d27-7032efe0920b
-- title:
--   Section sorting on the resolution of uv=varpi^e
-- statement:
--   Let $O$ be a discrete valuation ring (a domain), let $\varpi \in O$ generate the maximal ideal, i.e. $\mathfrak{m}_O = (\varpi)$, and let $e$ be a natural number. Write $\mathrm{CrossingQuotient}\,W\,s$ for $W[X_0,X_1]/(X_0X_1 - s)$, and let `Resolution ϖ e` be the scheme obtained as the colimit of the gluing diagram `glueDiagram ϖ e`, viewed over $\operatorname{Spec} O$ through `Resolution.toSpec ϖ e`, which is `Resolution.toCrossing ϖ e` followed by the morphism induced by the structure map $O \to \mathrm{CrossingQuotient}\,O\,(\varpi^{e})$. Assume given ideal sheaf data $F_0,\dots,F_e$ on `Resolution ϖ e` satisfying the chart table: for every chart index $i \in \mathrm{Fin}\,e$ and every $k$, the pullback of $F_k$ along the chart morphism `Resolution.ι ϖ e i` from $\operatorname{Spec}(\mathrm{CrossingQuotient}\,O\,\varpi)$ is the ideal sheaf data attached, via the inverse of the global-sections isomorphism, to the ideal $(V\,\varpi)$ if $k = i$, to $(U\,\varpi)$ if $k = i+1$, and to the unit ideal otherwise, where $U\,\varpi$ and $V\,\varpi$ are the two coordinate elements of $\mathrm{CrossingQuotient}\,O\,\varpi$. Let $t \colon \operatorname{Spec} O \to$ `Resolution ϖ e` be a section of the structure morphism, and let $\psi \colon \mathrm{CrossingQuotient}\,O\,(\varpi^{e}) \to O$ be a ring homomorphism such that $t$ followed by `Resolution.toCrossing ϖ e` is the morphism induced by $\psi$. Then for each $k \in \{0,\dots,e\}$, the image under $t$ of the closed point of $\operatorname{Spec} O$ lies in the support of $F_k$ if and only if $k$, read in $\mathbb{N}_\infty$, equals the additive valuation of $\psi(U\,(\varpi^{e}))$.
--
--   This is the position-versus-valuation dictionary on the standard toric resolution of the $A_{e-1}$ singularity $uv = \varpi^{e}$: an $O$-section meets exactly the component of the special fibre whose index is the valuation of the $u$-coordinate of its image in the singular model. It is used in the construction of chart presentations of stalks for the resolved Deligne–Rapoport models of modular curves, both with and without extra level at the ramified prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_CrossingQuotient_Resolution_mem_support_iff_eq_addVal_of_comp_toCrossing_eq.lean

import Mathlib
import Definitions.Def_MvPolynomial_CrossingResolutionScheme

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

universe u

theorem MvPolynomial.CrossingQuotient.Resolution.mem_support_iff_eq_addVal_of_comp_toCrossing_eq
    {O : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}) (e : ℕ)
    (F : Fin (e + 1) → (Resolution ϖ e).IdealSheafData)
    (hF : ∀ (i : Fin e) (k : Fin (e + 1)), (F k).comap (Resolution.ι ϖ e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ϖ))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ϖ} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ϖ} else ⊤)))
    (t : Spec (CommRingCat.of O) ⟶ Resolution ϖ e) (ht : t ≫ Resolution.toSpec ϖ e = 𝟙 _)
    (ψ : CrossingQuotient O (ϖ ^ e) →+* O)
    (hψ : t ≫ Resolution.toCrossing ϖ e = Spec.map (CommRingCat.ofHom ψ))
    (k : Fin (e + 1)) :
    t.base (IsLocalRing.closedPoint O) ∈ (F k).support ↔
      ((k : ℕ) : ℕ∞) = IsDiscreteValuationRing.addVal O (ψ (CrossingQuotient.U (ϖ ^ e))) := by sorry
