-- Prove2me | Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkCountAtomExpansionAe
-- name    : Kyprianou.Ch06.finiteBooleanMarkCountAtomExpansionAe
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T07:23:52.870282+00:00
-- url     : https://prove2.me/theorems/d4a0e8e1-7647-4d6c-b00d-a78dac526ffd
-- title:
--   Lemma 6.18: finite Boolean mark atom expansion of each overlapping marked-Poisson count
-- statement:
--   At every time, the marked-Poisson count of any given member B_i of a finite overlapping family equals the sum of counts over the disjoint Boolean membership atoms whose patterns contain i, almost surely. Combines the separately Proved measurable/disjoint atom decomposition with finite disjoint count additivity. This is the spatial reconstruction step for the arbitrary overlapping-mark rectangle representation in Lemma 6.18.
-- source:
--   Kyprianou (2006), Lemma 6.18(ii), printed pp.160–161, finite overlapping mark cylinder decomposition.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_finiteBooleanMarkAtomsMeasurableDisjointCover
import Theorems.Thm_Kyprianou_Ch06_finiteDisjointMarkedCountAdditivityAe
open MeasureTheory
open scoped NNReal
set_option autoImplicit false

theorem Kyprianou.Ch06.finiteBooleanMarkCountAtomExpansionAe
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) (n : Measure E)
    (N : Omega → NNReal → Set E → Nat)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (m : Nat) (B : Fin m → Set E)
    (hB : ∀ i, MeasurableSet (B i)) (i : Fin m) :
    ∀ᵐ omega ∂P, ∀ t : NNReal,
      N omega t (B i) =
        ∑ S ∈ (Finset.univ.filter (fun S : Finset (Fin m) => i ∈ S)),
          N omega t {x : E | ∀ j : Fin m,
            (x ∈ B j ↔ j ∈ S)} := by sorry
