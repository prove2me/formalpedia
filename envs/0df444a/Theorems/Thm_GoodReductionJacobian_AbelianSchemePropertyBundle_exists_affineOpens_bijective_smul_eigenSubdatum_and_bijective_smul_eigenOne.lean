-- Prove2me | Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne
-- name    : GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:49.54035+00:00
-- url     : https://prove2.me/theorems/303e011e-405e-5700-b13e-be81b8dbc113
-- title:
--   Local multiplicative frames for eigenparts of [n]_*𝒪_A
-- statement:
--   Let $K$ be an algebraically closed field, $A$ a scheme, $f : A \to \operatorname{Spec} K$ a morphism, and $L$ a relative group law on $f$, i.e. a functorial group structure on the sets $\{\varphi : T \to A \mid \varphi \circ f = t\}$ of $T$-points over $\operatorname{Spec} K$, compatible with base change; assume $L$ is commutative, that $f$ satisfies `AbelianSchemePropertyBundle` ($f$ smooth and proper with connected fibres and admitting a relative group law), and that $f$ is smooth of relative dimension $g$. Let $n$ be a natural number with $n \neq 0$ in $K$, and assume the hypothesis $hG$: for every $n$-torsion point $x$ of $L$ over the identity of $\operatorname{Spec} K$, translation by $x$ followed by the multiplication-by-$n$ endomorphism $[n] =$ `L.schemeNsmul n` equals $[n]$. Two assertions are made. First, for all functions $\chi, \psi$ from the $K$-points of $f$ to $K$ that are $n$-smul characters (each is $1$ outside the $n$-torsion subset, takes the value $1$ at the identity, and is multiplicative on the $n$-torsion subset) and every point $y$ of $A$, there are an affine open $V \ni y$ and sections $s \in (L.\mathrm{eigenSubdatum}\ n\ hG\ \chi)(V)$ and $t \in (L.\mathrm{eigenSubdatum}\ n\ hG\ \psi)(V)$ — these $\mathcal{O}$-module presheaves being the eigen-submodules $L.\mathrm{eigenSubmodule}$ inside the pushforward $[n]_*\mathcal{O}_A$, so that $s$ and $t$ are elements of $\Gamma(A, [n]^{-1}V)$ — such that for every affine open $W \le V$ the three maps $a \mapsto a \cdot s|_W$, $a \mapsto a \cdot t|_W$ and $a \mapsto a \cdot (st)|_W$, where $st = L.\mathrm{eigenMul}\ n\ hG\ s\ t$ is the product in $\Gamma(A, [n]^{-1}V)$ viewed in the $\chi\psi$-eigen-submodule, are bijections from $\Gamma(A, W)$ onto the respective eigen-submodules over $W$. Second, for every affine open $U$ the map $a \mapsto a \cdot L.\mathrm{eigenOne}\ n\ hG\ U$, multiplication of the unit section $1 \in \Gamma(A, [n]^{-1}U)$ lying in the eigen-submodule for the trivial character, is a bijection from $\Gamma(A, U)$ onto that eigen-submodule over $U$.
--
--   This packages the local structure of the eigen-decomposition of $[n]_*\mathcal{O}_A$ along the multiplication-by-$n$ isogeny of an abelian variety with $n$ invertible: each eigenpart is locally free of rank one on affines, with frames that multiply correctly, and the part belonging to the trivial character is $\mathcal{O}_A$ itself (the invariants of the $A[n]$-action). It is obtained by combining the pointwise unit statement `exists_affineOpens_isUnit_eigenSubdatum` with `bijective_smul_eigenOne`, and is used by `exists_affSES_filtration_pushforwardUnit_schemeNsmul`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.AbelianSchemePropertyBundle.exists_affineOpens_bijective_smul_eigenSubdatum_and_bijective_smul_eigenOne
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) :
    (∀ (χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K),
      L.IsNsmulCharacter n χ → L.IsNsmulCharacter n ψ →
      ∀ y : A, ∃ V : A.affineOpens, y ∈ V.1 ∧
        ∃ (s : (L.eigenSubdatum n hG χ).obj V.1) (t : (L.eigenSubdatum n hG ψ).obj V.1),
          ∀ (W : A.affineOpens) (hW : W.1 ≤ V.1),
            Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG χ).res hW s) ∧
            Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG ψ).res hW t) ∧
            Function.Bijective (fun a : Γ(A, W.1) => a • (L.eigenSubdatum n hG (χ * ψ)).res hW (L.eigenMul n hG s t))) ∧
    (∀ U : A.affineOpens, Function.Bijective (fun a : Γ(A, U.1) => a • L.eigenOne n hG U.1)) := by sorry
