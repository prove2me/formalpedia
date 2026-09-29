-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
-- name    : ModularCurve.PlaceSpecialization.exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0a7b97b1-dcf5-59cd-abdf-5627be33336e
-- title:
--   Reduction of places commutes with both degeneracy legs
-- statement:
--   Fix $N\ge 1$, a valuation subring $A$ of $\overline{\mathbb{Q}}=\mathrm{AlgebraicClosure}\ \mathbb{Q}$ with residue field $k$, and a prime $q$ (with $Nq\neq 0$). Assume the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` of `modularFunctionFieldBar N` into `modularFunctionFieldBar (N*q)` over $\overline{\mathbb{Q}}$ are integral, and likewise the two characteristic-$\ell$ embeddings `heckeAlphaC`, `heckeBetaC` of `modularFunctionFieldC k N` into `charLDegeneracyRoof k N q`; assume every nonzero element of `modularFunctionFieldBar N`, of `modularFunctionFieldBar (N*q)` and of the roof has a divisor of degree $0$ (class `HasPrincipalDivisors`), and that every place $Y$ of the roof over $k$ satisfies $\deg Y=\dim_k Y.\mathrm{ResidueField}=1$. Let $R_1$ be a regular prolongation of $A$ to `modularFunctionFieldBar N` with residue field `modularFunctionFieldC k N`, and $r_1$ a map on places such that $(r_1)_*$ of the divisor of any $f\in R_1.\mathrm{integers}$ with nonzero residue is the divisor of $R_1.\mathrm{residue}\,f$; let $R$, $r$ be such data for `modularFunctionFieldBar (N*q)` and the roof. Assume $R$ restricts to $R_1$ along each of $\alpha$, $\beta$, i.e. $\alpha f,\beta f\in R.\mathrm{integers}$ with residues $\bar\alpha(\bar f)$, $\bar\beta(\bar f)$, and that for every place $v$ the fibre divisors $\alpha^{*}\langle v\rangle$ and $\bar\alpha^{*}\langle r_1 v\rangle$ have equal degree, similarly for $\beta$. Then for every place $v$ one has $r_*(\alpha^{*}\langle v\rangle)=\bar\alpha^{*}\langle r_1v\rangle$ and $r_*(\beta^{*}\langle v\rangle)=\bar\beta^{*}\langle r_1v\rangle$, and for every place $W$ upstairs the restriction of $rW$ along $\bar\alpha$ is $r_1$ of the restriction of $W$ along $\alpha$, and likewise for $\beta$.
--
--   This is the functoriality of Deuring's reduction of places of a modular function field modulo a place of the constant field, stated simultaneously at the level of fibre divisors and at the level of places, for both legs of the $q$-degeneracy correspondence on $X_0(N)$. It feeds the comparison of the Hecke correspondence $T_q$ upstairs with its characteristic-$\ell$ fibre, via [`ModularCurve.mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation`](thm.html#ModularCurve.mapDomain_heckeDivBar_single_eq_heckeDivFibre_of_regularProlongation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2.lean

import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ValuationSubring AlgebraicCurve IsLocalRing

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

theorem ModularCurve.PlaceSpecialization.exists_spRoof_pullbackAlong_restrictAlong_compat_of_exists_placeMap_fullC_v2
    (N : ℕ) [NeZero N]
    (A : ValuationSubring (AlgebraicClosure ℚ))
    (q : ℕ) [hq' : Fact q.Prime] [NeZero (N * q)]
    (hαq : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
    (hβq : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
    (hαc : HeckeAlphaCIntegral (ResidueField ↥A) N q)
    (hβc : HeckeBetaCIntegral (ResidueField ↥A) N q)
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))]
    [HasPrincipalDivisors (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q)]
    (hdeg1 : ∀ Y : Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q),
      Y.deg = 1)
    (R₁ : RegularProlongation A (modularFunctionFieldBar N)
      (modularFunctionFieldC (ResidueField ↥A) N))
    (r₁ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
      → Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N))
    (hr₁ : ∀ f : R₁.integers, R₁.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar N)) →
      ∀ Q, Finsupp.mapDomain r₁ D Q = Q.ord (R₁.residue f))
    (R : RegularProlongation A (modularFunctionFieldBar (N * q))
      (charLDegeneracyRoof (ResidueField ↥A) N q))
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (ResidueField ↥A) (charLDegeneracyRoof (ResidueField ↥A) N q))
    (hr : ∀ f : R.integers, R.residue f ≠ 0 →
      ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
        (∀ P, D P = P.ord (f : modularFunctionFieldBar (N * q))) →
      ∀ Q, Finsupp.mapDomain r D Q = Q.ord (R.residue f))
    (hRα : ∀ f : R₁.integers,
      ∃ h : heckeAlphaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeAlphaC (ResidueField ↥A) N q (R₁.residue f))
    (hRβ : ∀ f : R₁.integers,
      ∃ h : heckeBetaBar (AlgebraicClosure ℚ) N q (f : modularFunctionFieldBar N) ∈ R.integers,
        R.residue ⟨_, h⟩ = heckeBetaC (ResidueField ↥A) N q (R₁.residue f))
    (hdegα : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc (Finsupp.single (r₁ v) 1)))
    (hdegβ : ∀ v, Divisor.degree
        (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
      = Divisor.degree
        (Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc (Finsupp.single (r₁ v) 1))) :
    (∀ v, Finsupp.mapDomain r
          (Divisor.pullbackAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq (Finsupp.single v 1))
        = Divisor.pullbackAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
            (Finsupp.single (r₁ v) 1))
    ∧ (∀ v, Finsupp.mapDomain r
          (Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq (Finsupp.single v 1))
        = Divisor.pullbackAlong (heckeBetaC (ResidueField ↥A) N q) hβc
            (Finsupp.single (r₁ v) 1))
    ∧ (∀ W, (r W).restrictAlong (heckeAlphaC (ResidueField ↥A) N q) hαc
        = r₁ (W.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hαq))
    ∧ ∀ W, (r W).restrictAlong (heckeBetaC (ResidueField ↥A) N q) hβc
        = r₁ (W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβq) := by sorry
