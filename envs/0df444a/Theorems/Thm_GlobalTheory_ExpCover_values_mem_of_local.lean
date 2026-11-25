-- Prove2me | Theorems.Thm_GlobalTheory_ExpCover_values_mem_of_local
-- name    : GlobalTheory.ExpCover.values_mem_of_local
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:19.953487+00:00
-- url     : https://prove2.me/theorems/41184e77-c433-4cb8-8c18-31ec8a7c1cb3
-- title:
--   Exp Cover: values mem of local
-- statement:
--   The Exp Cover construction uses the values mem of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuesMemOfLocal.lean#L78-L276
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ValuesMemOfLocal.lean#L78-L276

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MaximalIdealEqJointEigen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValuesMemOfLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPolynomial
open GlobalTheory GlobalTheory.ExpCover
set_option autoImplicit false
open MvPolynomial

theorem GlobalTheory.ExpCover.values_mem_of_local {l : ℕ} [Fact l.Prime] {O I G V W : Type} [CommRing O]
    [IsDomain O] [IsPrincipalIdealRing O] [Mul G]
    [AddCommGroup V] [Module O V] [Module.Finite O V] [AddCommGroup W] [Module (PadicAlgCl l) W]
    (M : Submodule O (G → V)) [hm : Module (MvPolynomial I O) M] [@IsScalarTower O (MvPolynomial I O) M _ hm.toSMul _]
    [Module.Finite O M]
    (emb : O →+* PadicAlgCl l) (hemb : Function.Injective emb)
    (h1 : ∀ c, ‖emb c‖ ≤ 1) (hu : ∀ c, ‖emb c‖ = 1 → IsUnit c) (b : V →ₛₗ[emb] W) (hb : Function.Injective b)
    (hli : ∀ (n : ℕ) (y : Fin n → V), LinearIndependent O y → LinearIndependent (PadicAlgCl l) fun j => b (y j))
    (tr : I → Finset G) (cst : I → O)
    (hX : ∀ i (f : M) g, (((X i : MvPolynomial I O) • f : M) : G → V) g = cst i • ∑ s ∈ tr i, (f : G → V) (g * s))
    (U : Submodule O V) (S : Submodule (PadicAlgCl l) (G → W))
    (hS : ∀ i, ∀ u ∈ S, _root_.GlobalTheory.ExpCover.transOp (emb (cst i)) (tr i) u ∈ S)
    (x : M) (hx : (fun g => b ((x : G → V) g)) ∈ S) (a : O) (J : ℕ) (D : Set M) (hD : ∀ y ∈ D, ∀ g, (y : G → V) g ∈ U)
    (hloc : ∀ (m : Ideal (MvPolynomial I O)) (hmax : m.IsMaximal) (θ : I → PadicAlgCl l), (∀ i, ‖θ i‖ ≤ 1) →
      (∀ p, p ∈ m ↔ ‖eval₂ emb θ p‖ < 1) →
      (∃ v ∈ S, v ≠ 0 ∧ ∀ i g, emb (cst i) • ∑ s ∈ tr i, v (g * s) = θ i • v g) →
      ∀ y : LocalizedModule (haveI := hmax.isPrime; m.primeCompl) M,
        ∃ x' ∈ D, ∃ s : (haveI := hmax.isPrime; m.primeCompl),
          LocalizedModule.mk x' s = (algebraMap O (MvPolynomial I O) a) ^ J • y) :
    ∀ g, ((a ^ J • x : M) : G → V) g ∈ U := by sorry
