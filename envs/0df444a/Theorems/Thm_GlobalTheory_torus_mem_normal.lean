-- Prove2me | Theorems.Thm_GlobalTheory_torus_mem_normal
-- name    : GlobalTheory.torus_mem_normal
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:24:36.067905+00:00
-- url     : https://prove2.me/theorems/4e193fcd-af6b-4765-b7bc-de5eacaddbef
-- title:
--   Global Theory: torus mem normal
-- statement:
--   The Global Theory construction uses the torus mem normal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L178-L213
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/UniformizerPowerTorusMemNormalUnitarySubgroup.lean#L178-L213

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FIwasawa
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_InvMemDoubleCosetAndComm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_UniformizerPowerTorusMemNormalUnitarySubgroup
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG Matrix
noncomputable section
open GlobalTheory
open Formalism.UG.P GlobalTheory.TorusNormal

theorem GlobalTheory.torus_mem_normal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ N : Subgroup (Formalism.UG.GU σ n), N.Normal →
    Formalism.UG.KU σ n ≤ N → (∀ u : Formalism.UG.GU σ n, Formalism.UG.IsUnipU u → u ∈ N) → ∀ (c : Fin n → ℤ),
    (∀ i : Fin n, c i.rev = -c i) → ∀ t : Formalism.UG.GU σ n,
    ((t : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) = Matrix.diagonal (fun i => ϖ ^ c i) → t ∈ N := by sorry
