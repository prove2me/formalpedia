-- Prove2me | Theorems.Thm_InfoDerivQT_maximal_sets_same_card
-- name    : InfoDerivQT.maximal_sets_same_card
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-02T13:25:24.851976+00:00
-- url     : https://prove2.me/theorems/8cbedf72-734a-4468-9ca0-1d3b0d087df2
-- title:
--   Lemma 32 — all maximal sets of perfectly distinguishable pure states have the same size
-- statement:
--   Let $T$ satisfy the six principles and $A$ a system. If $\{\varphi_i\}_{i=1}^N$ and $\{\psi_j\}_{j=1}^M$ are both maximal sets of perfectly distinguishable pure states of $A$, then
--
--   $$N=M.$$
--
--   The common value is the **informational dimension** $d_A$ of the system.
-- source:
--   G. Chiribella, G. M. D'Ariano, P. Perinotti, *Informational derivation of quantum theory*, Phys. Rev. A 84, 012311 (2011), https://doi.org/10.1103/PhysRevA.84.012311 (arXiv:1011.6451), p. 012311-16, Sec. VII, Lemma 32

import Mathlib
import Definitions.Def_InfoDerivQT_principles

namespace InfoDerivQT
theorem maximal_sets_same_card (T : OPT) (hT : T.SatisfiesPrinciples) (A : T.Sys)
    {N M : ℕ} (φ : Fin N → Vec (T.size A)) (ψ : Fin M → Vec (T.size A))
    (hφ : T.IsMaximalPerfDistPure A φ) (hψ : T.IsMaximalPerfDistPure A ψ) :
    N = M := by sorry
end InfoDerivQT
