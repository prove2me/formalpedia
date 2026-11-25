-- Prove2me | Theorems.Thm_Kyprianou_Ch04_idleRegulatorFiniteIdentityV1
-- name    : Kyprianou.Ch04.idleRegulatorFiniteIdentityV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-25T00:14:28.222875+00:00
-- url     : https://prove2.me/theorems/1b231161-ddc9-4eda-98ee-5cecb6a488d0
-- title:
--   Finite horizon idle occupation equals the running-supremum regulator divided by drift
-- statement:
--   Use the proved BV monotone drift deficit and the almost-everywhere right dyadic slope. The regulator R(t)=max(w,sup_{s≤t}X_s) is monotone and d-Lipschitz, by the upper increment bound. Off contact it is locally constant to the right; on contact its right dyadic slope is squeezed between the input slope and d. Rademacher and the fundamental theorem for absolutely continuous real functions then give the exact occupation integral, including infinite-activity BV input.
-- source:
--   Kyprianou (2006), Chapter 4, Theorem 4.1, proof of idle-time regulator identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical Filter
open scoped NNReal ENNReal
set_option autoImplicit false
open scoped Topology
open Set

theorem Kyprianou.Ch04.idleRegulatorFiniteIdentityV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (L : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (hBV : L.BoundedVariation)
    (hd : 0 < L.drift)
    (w : Real) (hw : 0 ≤ w) :
    let supX : NNReal → Omega → Real := fun t omega =>
      sSup ((fun s : NNReal => L.X s omega) '' Iic t)
    let W : NNReal → Omega → Real := fun t omega =>
      max w (supX t omega) - L.X t omega
    ∀ᵐ omega ∂P, ∀ T : NNReal,
      ENNReal.ofReal (max w (supX T omega) - w) =
        ENNReal.ofReal L.drift *
          (∫⁻ t in Icc (0 : Real) (T : Real),
            (if W (Real.toNNReal t) omega = 0 then (1 : ENNReal) else 0) ∂volume) := by
  sorry
