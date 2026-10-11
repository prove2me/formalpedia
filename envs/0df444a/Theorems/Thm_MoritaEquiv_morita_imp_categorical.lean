-- Prove2me | Theorems.Thm_MoritaEquiv_morita_imp_categorical
-- name    : MoritaEquiv.morita_imp_categorical
-- status  : Open
-- author  : @Alien60
-- created : 2026-10-10T13:02:54.954887+00:00
-- url     : https://prove2.me/theorems/8f7681ff-fa0c-48d1-814b-c133b37c23db
-- title:
--   Morita equivalence implies categorical equivalence
-- statement:
--   If two many-sorted first-order theories $T_1,T_2$ are Morita equivalent (finite chains of Morita extensions ending in logically equivalent theories over a common signature, up to renaming), then $\mathrm{Mod}(T_1)\simeq\mathrm{Mod}(T_2)$, with elementary embeddings as arrows.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675 (numbering as in arXiv v1), §5, Theorem 5.1

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- Barrett–Halvorson, Theorem 5.1: Morita equivalence entails categorical equivalence,
i.e. Morita equivalent theories have equivalent categories of models
(arrows: elementary embeddings). -/
theorem morita_imp_categorical {L₁ L₂ : Sig} (T₁ : Theory L₁) (T₂ : Theory L₂)
    (h : MoritaEquivalent T₁ T₂) : CategoricallyEquivalent T₁ T₂ := by sorry

end MoritaEquiv
