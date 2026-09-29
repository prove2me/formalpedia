-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/1c265520-896f-5a60-b13b-fcd8cba9dc0e
-- title:
--   Hecke-equivariant component map and toric monodromy detection
-- statement:
--   Let $N$ be a nonzero natural number and $q$ a prime with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a nonunit of $A$, so that $\kappa = \mathrm{ResidueField}\,A$ has characteristic $q$; the groups $\mathrm{JZero}(Nq)$ and $\mathrm{JZero}(N)$ carry the Hecke-module structures of `heckeModuleBar` over $\mathrm{HeckeAlg} = \mathrm{MvPolynomial}\ \mathrm{Nat.Primes}\ \mathbb{Z}$. Fix a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\ \kappa\ N$ whose members are exactly the places satisfying `IsSupersingularPlace q N`, and write $\Sigma = W.\mathrm{map}$ of the node-pair embedding attached to the arithmetic Frobenius semilinear automorphism $\mathrm{arithFrobC}\ q\ \kappa\ N$; assume $\Sigma$ is stable under that automorphism, i.e. $(g\cdot s_1, g\cdot s_2)\in\Sigma$ for all $s\in\Sigma$. Fix modular polynomial data $\mathrm{data}$ of level $q$ (a monic $\Phi$ of degree $\psi(q)$ with $\Phi(j,j_q)=0$) satisfying the Kronecker congruence $\Phi \equiv (C X^q - X)(C X - X^q) \bmod q$, integrality hypotheses $h\alpha,h\beta$ for the two degeneracy maps from level $N$ to level $Nq$, a place specialization $P$ over the residue map $A \to \kappa$, a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws), satisfies the regularity law and the node-value law for $W$ and the fixed-point order law, a width function $e$ on places, and additive maps $\mathrm{comp}$ from the inertia invariants $\mathrm{JZero}(Nq)^{I_A}$ (invariants under the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$) to the combinatorial component group $\Phi_e$ of the widths $s \mapsto e(s_1)$ on $\Sigma$ (the dual of the character lattice modulo the image of the Gram map), and $\mathrm{sp}$ from the same group to $\mathrm{GluedPic0}\ \kappa\ (\mathrm{modularFunctionFieldC}\ \kappa\ N)\ \Sigma$, such that $\mathrm{comp}$ is surjective, $\mathrm{comp}\,x = 0$ holds exactly when $x$ is a good class for $\Sigma$ (representable by a degree-zero divisor all of whose support places are strictly of the first or second kind and whose glue data are admissible), and $\mathrm{sp}$ is a glued specialization for $\Sigma$. Then there is a $\mathrm{HeckeAlg}$-module structure on $\Phi_e$ for which, first, $\mathrm{comp}(T\cdot x) = T\cdot \mathrm{comp}(x)$ whenever $T \in \mathrm{HeckeAlg}$, $x \in \mathrm{JZero}(Nq)^{I_A}$ and $T\cdot x$ again lies in $\mathrm{JZero}(Nq)^{I_A}$, and, second, for every maximal ideal $\mathfrak{m}$ of $\mathrm{HeckeAlg}$ with vanishing $\mathfrak{m}$-torsion in $\Phi_e$, every $x$ in the $\mathfrak{m}$-torsion of $\mathrm{JZero}(Nq)$ killed by some positive integer prime to $q$ which lies in $\mathrm{JZero}(Nq)^{I_A}$ and satisfies $\mathrm{comp}\,x = 0$ and $\mathrm{toPic0Pair}_\Sigma(\mathrm{sp}\,x) = 0$ belongs to the toric monodromy part $\mathrm{toricMonodromyPart}\ q\ (I_A)$, the $\mathrm{HeckeAlg}$-span of the differences $\sigma\cdot y - y$ with $\sigma$ in the inertia subgroup and $y$ killed by a positive integer coprime to $q$.
--
--   This is the packaging, at a place of $\overline{\mathbb{Q}}$ above $q$, of the Hecke-equivariance of the component map of $J_0(Nq)$ at $q$ together with the detection of toric monodromy at maximal ideals of the Hecke algebra whose torsion in the component group vanishes, in the style of Ribet's analysis of the special fibre at $q$ and of Grothendieck's monodromy filtration. It is used by the statements asserting the existence of width, component-map and glued-specialization data for the supersingular node configuration.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel.lean

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false

noncomputable section

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_heckeModule_componentGroup_toricMonodromyPart_mem_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∃ _ : Module HeckeAlg
            (componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e)),
          (∀ (T : HeckeAlg) (x : ↥(inertiaInvariants A (N * q)))
            (hx : T • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp ⟨T • (x : JZero (N * q)), hx⟩ = T • comp x) ∧
          (∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal →
            heckeTorsion (componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
                𝔪 = ⊥ →
              ∀ x ∈ heckeTorsion (JZero (N * q)) 𝔪,
                PrimeToTorsion q x →
                  ∀ h : x ∈ inertiaInvariants A (N * q), comp ⟨x, h⟩ = 0 →
                    GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                        (sp ⟨x, h⟩) = 0 →
                      x ∈ toricMonodromyPart (J := JZero (N * q)) q
                        (A.inertiaSubgroupIn ℚ))) := by sorry
