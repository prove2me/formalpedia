-- Prove2me | Theorems.Thm_ModularCurve_genDiffModL_dia_inv_smul_D
-- name    : ModularCurve.genDiffModL_dia_inv_smul_D
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/a58b3914-161f-5a2b-a0b5-8a54dd282fb9
-- title:
--   Diamond operator on differentials sends dlog to dlog of the pullback
-- statement:
--   Let $K$ be a field, $p$ a prime and $M$ a nonzero natural number with $p \mid M$, let $H$ be a subgroup of $(\mathbf{Z}/M)^\times$, let $S$ be a set of natural numbers and let $e \in (\mathbf{Z}/M)^\times$. Write $H' = \mathrm{infSubgroup}$, the image of $H$ under the reduction $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$, write $\Gamma_{H'} \le \mathrm{SL}_2(\mathbf{Z})$ for the image in $\mathrm{SL}_2(\mathbf{Z})$ of the preimage of $H'$ under the lower-right-entry character $\Gamma_0(M/p) \to (\mathbf{Z}/(M/p))^\times$, and let $F = \mathrm{qExpFunctionFieldC}\,K\,\Gamma_{H'}$ be the subfield of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}\,K\,p_f / \mathrm{intSeriesC}\,K\,p_g$ of $K$-specialisations of integral $q$-expansions of modular forms of a common weight for $\Gamma_{H'}$ (with $\mathrm{intSeriesC}\,K\,p_g \neq 0$). Let $\bar e$ be the image of $e$ in $(\mathbf{Z}/(M/p))^\times$ and put $\sigma = \mathrm{diamondActionModL}\,K\,(M/p)\,H'\,(\mathrm{gammaLift}(M/p, \bar e^{-1}))$, the value at a chosen element of $\Gamma_0(M/p)$ with lower-right entry $\bar e^{-1}$ of the chosen monoid homomorphism $\Gamma_0(M/p) \to \mathrm{Aut}_K(F)$ satisfying $\mathrm{IsDiamondPullbackModL}$ (the trivial homomorphism if no such exists). Then for every $f \in F$, the operator attached by $\mathrm{genDiffModL}$ to the generator $\mathrm{dia}\,e$, that is the $K$-linear pullback of Kähler differentials along $\sigma$, sends $f^{-1} \cdot Df$ to $\sigma(f)^{-1} \cdot D(\sigma f)$, where $D : F \to \Omega_{F/K}$ is the universal derivation. The diamond branch of $\mathrm{genDiffModL}$ does not depend on $S$.
--
--   This is the compatibility of the diamond operator $\langle e \rangle$ on the differentials of the $q$-expansion function field of $X_{H'}(M/p)$ with logarithmic differentials: $\langle e\rangle(\mathrm{dlog}\,f) = \mathrm{dlog}(\sigma f)$, the orientation of $\sigma$ being the one fixed in the definition of the diamond action. It feeds the assembly of Hecke- and diamond-equivariant data on differentials used in the construction of the torsion homomorphism into polarised differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genDiffModL_dia_inv_smul_D.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.genDiffModL_dia_inv_smul_D
    (K : Type*) [Field K] (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (S : Set ℕ) (e : (ZMod M)ˣ)
    (f : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :
    ModularCurve.genDiffModL K p M H hpM S (CohCarrier.Gen.dia e)
        (f⁻¹ • KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) f) =
      (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)⁻¹) f)⁻¹ •
        KaehlerDifferential.D K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))
          (haveI : NeZero (M / p) := ⟨Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (NeZero.pos M) hpM) (Fact.out : p.Prime).pos)⟩;
            ModularCurve.diamondActionModL K (M / p) (ModularCurve.infSubgroup p M H hpM)
              (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) e)⁻¹) f) := by sorry
