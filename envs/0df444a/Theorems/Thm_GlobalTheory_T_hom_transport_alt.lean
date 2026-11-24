-- Prove2me | Theorems.Thm_GlobalTheory_T_hom_transport_alt
-- name    : GlobalTheory.T.hom_transport_alt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:53:24.484658+00:00
-- url     : https://prove2.me/theorems/0c624261-d80b-49cb-9c0d-c23f9026fdd5
-- title:
--   T: hom transport alt
-- statement:
--   The T construction uses the hom transport alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransportStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransportStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransportStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hom_transport_alt : ∀ (O O' : Type) [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') (I : NumD.Hom f N N'), (∀ g, ∃! g', I.Rel g g') ∧ (∀ g h g' h', I.Rel g g' → I.Rel h h' → I.Rel (g * h) (g' * h')) ∧ (∀ y, I.Rel (N.io y) (N'.io (I.e y))) ∧ (∀ k (p q : N.QT k) (p' q' : N'.QT k), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → q'.1.1.toAdd = I.e q.1.1.toAdd → I.Rel q.1.2 q'.1.2 → N'.wp p' q' = Units.map f.toMonoidHom (N.wp p q)) ∧ ∀ m, Odd m → ∀ (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → ∀ χ, N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) ∧ ∀ h h', I.Rel h h' → N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) := by sorry
