-- Prove2me | Theorems.Thm_LPCA_localization_nontrivial_iff
-- name    : LPCA.localization_nontrivial_iff
-- status  : Proved
-- author  : @kaiyue
-- created : 2026-10-20T22:46:03.900183+00:00
-- url     : https://prove2.me/theorems/eeb731dc-96dc-443a-8f5e-358cf2bd83cf
-- title:
--   Lemma 2.1 — Nonzero localization exactly at a face
-- statement:
--   Let $k$ be any field and $\Delta$ a finite downward-closed face family on a finite ambient vertex set. The actual quotient face ring localized at the product $x_F$ is nontrivial if and only if $F$ is a face:
--
--   $$k[\Delta]_{x_F}\ne0\quad\Longleftrightarrow\quad F\in\Delta.$$
--
--   No assumption that all singleton faces occur is needed. The assertion includes $F=\varnothing$ and void face families.
-- source:
--   https://arxiv.org/abs/2609.02858v1, Lemma 2.1, Section 2.1.

import Definitions.Def_LPCA
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
universe u

namespace LPCA
theorem localization_nontrivial_iff
    {V : Type u} [DecidableEq V] [Fintype V]
    (k : Type u) [Field k] (K : Complex V) (F : Finset V) :
    Nontrivial (LocalizedFaceRing k K F) ↔ F ∈ K.faces := by sorry
end LPCA
