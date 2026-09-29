-- Prove2me | Theorems.Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_frobFam
-- name    : MvFormalGroup.BigWittLaw.subst_pow_subst_frobFam
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/7d1e6a72-a65a-5197-8c2b-1b3abeaab38f
-- title:
--   Frobenius mathbf Fₙ of the big Witt law on ω-curves
-- statement:
--   Let $R$ be a commutative ring, let $n$ be a natural number with $0 < n$, and let $G$ be a multivariate formal power series over $R$ in the variables indexed by $\mathbb N$ whose constant term vanishes. Let $\omega$ denote the substitution family $m \mapsto X^{m+1}$ of one-variable power series over $R$, and let [`MvFormalGroup.BigWittLaw.frobFam R n`](def/MvFormalGroup_BigWittFrobenius.html#L432) denote the family $m \mapsto$ the power series attached to the integral polynomial `frobPoly n m`, the latter being the coefficient of degree $m+1$ of the product $\prod_{k < n(m+1)}$ `frobFactor n k`, with its integer coefficients mapped into $R$. The assertion is the equality of two one-variable power series over $R$: substituting $\omega$ into the power series obtained from $G$ by substituting the family `frobFam R n` gives the same result as applying `MvPowerSeries.expand n`, i.e. the substitution $X \mapsto X^{n}$, to the power series obtained by substituting $\omega$ into $G$. In the classical notation, $(G \circ \mathbf F_n)(\omega(t)) = G(\omega(t^{n}))$.
--
--   The family $\omega$ records the big Witt coordinates of $(1-tT)^{-1}$, so the statement says that the $n$-th Frobenius operator of the big Witt formal group law carries the curve $\omega(t)$ to $\omega(t^{n})$; on curves of a formal group, precomposition with $\mathbf F_n$ therefore acts as raising the parameter to the $n$-th power. It is used in the construction of integral Verschiebung elements in the Cartier module setting, through [`MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt`](thm.html#MvFormalGroup.CartierModule.exists_verschiebungInt_eq_of_tangent_eq_zero_of_algebra_padicInt).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_BigWittLaw_subst_pow_subst_frobFam.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_BigWittLaw
import Definitions.Def_MvFormalGroup_BigWittFrobenius
import Definitions.Def_MvFormalGroup_ArtinHasse

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.BigWittLaw.subst_pow_subst_frobFam
    (R : Type u) [CommRing R] (n : ℕ) (hn : 0 < n) (G : MvPowerSeries ℕ R)
    (hG0 : MvPowerSeries.constantCoeff G = 0) :
    MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1))
        (MvPowerSeries.subst (MvFormalGroup.BigWittLaw.frobFam R n) G)
      = MvPowerSeries.expand n hn.ne'
          (MvPowerSeries.subst (fun m : ℕ => (PowerSeries.X : PowerSeries R) ^ (m + 1)) G) := by sorry
