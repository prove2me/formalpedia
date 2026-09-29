-- Prove2me | Theorems.Thm_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius
-- name    : ModularCurve.genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/84d996f1-bccc-5177-8241-ecaab41abea0
-- title:
--   Uₚ on mod-p differentials sends dlog f to dlog σ f
-- statement:
--   Let $K$ be a field, $p$ a prime and $M$ a nonzero natural number with $p \mid M$, let $H \le (\mathbf{Z}/M)^\times$, let $S \subseteq \mathbf{N}$, and assume $K$ has characteristic $p$. Write $H'$ for [`ModularCurve.infSubgroup`](def/ModularCurve_XHDifferentialsModL.html#L246), the image of $H$ in $(\mathbf{Z}/(M/p))^\times$ under `ZMod.unitsMap` for $(M/p) \mid M$, write $\Gamma =$ [`CohCarrier.GammaH`](def/CohCarrier_Level.html#L133) $(M/p)$ $H'$, the subgroup of $\mathrm{SL}_2(\mathbf{Z})$ obtained by pushing forward along $\Gamma_0(M/p) \hookrightarrow \mathrm{SL}_2(\mathbf{Z})$ the preimage of $H'$ under the lower-right-entry character, and let $F =$ [`ModularCurve.qExpFunctionFieldC`](def/ModularCurve_X1.html#L101) $K\ \Gamma$, the intermediate field of $K((q))$ generated over $K$ by the ratios of integral $q$-expansions of modular forms of equal weight for $\Gamma$. Let $\Theta =$ [`ModularCurve.diffQExp`](def/ModularCurve_HeckeDifferential.html#L128) $F$ be the $F$-linear map $\Omega[F/K] \to K((q))$ obtained by lifting the derivation $q\,d/dq$ restricted along $F \subseteq K((q))$. Assume (i) there exists a $K$-linear endomorphism $C$ of $\Omega[F/K]$ with $\Theta(C\omega) =$ `qDecimate` $K\ p\ (\Theta\omega)$ for all $\omega$, where `qDecimate` keeps the coefficients in degrees divisible by $p$ and reindexes them, and (ii) $\Theta$ is injective. Let $f, f' \in F$ be such that the Laurent series of $f'$ is the coefficientwise image of that of $f$ under the Frobenius $x \mapsto x^p$ of $K$. Then [`ModularCurve.genDiffModL`](def/ModularCurve_XHDifferentialsModL.html#L266) evaluated at the generator `CohCarrier.Gen.U` $p$ — which by definition is the chosen Frobenius push-forward operator `frobPushDiffModL` on $\Omega[F/K]$ — sends $f^{-1} \cdot d f$ to $f'^{-1} \cdot d f'$.
--
--   This is the statement that the $U_p$ operator on differentials of the mod-$p$ modular curve of level $M/p$ with character group $H'$ fixes logarithmic differentials up to the Frobenius twist of their argument, the $q$-expansion form of the Cartier-invariance of $d\log$. It feeds the construction of the maps from torsion of the Jacobian to differentials used in the level-lowering and multiplicity-one arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.genDiffModL_U_self_inv_smul_D_of_coe_eq_coeffMap_frobenius
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (S : Set ℕ) [CharP K p]
    (hC : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩;
      ∃ C : Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K] →ₗ[K] Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K],
        ModularCurve.IsFrobPushDiff K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p C)
    (hinj : Function.Injective (ModularCurve.diffQExp (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))))
    (f f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
    (hf' : ((f' : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K) =
      ModularCurve.coeffMap (frobenius K p) ((f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) : LaurentSeries K)) :
    ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.U p Fact.out hpM)
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      f'⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f' := by sorry
