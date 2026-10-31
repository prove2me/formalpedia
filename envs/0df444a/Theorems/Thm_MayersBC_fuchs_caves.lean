-- Prove2me | Theorems.Thm_MayersBC_fuchs_caves
-- name    : MayersBC.fuchs_caves
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:57:22.389698+00:00
-- url     : https://prove2.me/theorems/631be8ae-81d2-4d3e-a5e9-24456e46db69
-- title:
--   Section d, p.8 — the minimum of $BW$ over all measurements is the fidelity $F$
-- statement:
--   Let $\rho_0, \rho_1$ be density matrices and $F(\rho_0, \rho_1) = \operatorname{Tr}\sqrt{\sqrt{\rho_0}\,\rho_1\sqrt{\rho_0}}$. Then:
--
--   1. for every measurement $\{M_j\}_{j\in J}$ (any finite $J$), with outcome distributions $p_b(j) = \operatorname{Tr}(M_j\rho_b)$,
--   $$
--   F(\rho_0, \rho_1) \le BW(p_0, p_1) ;
--   $$
--   2. some measurement (with finitely many outcomes) attains $BW(p_0, p_1) = F(\rho_0, \rho_1)$.
--
--   Together: the minimum of the Bhattacharyya–Wootters overlap over all measurements is the fidelity (Fuchs and Caves).
--
--   Differences from the source:
--   - encoding: the minimum of BW over all possible measurements is F → two clauses: F ≤ BW for every POVM with any finite outcome type, and equality for some POVM with outcomes Fin m; reason: these are the two halves of 'minimum'
--   - encoding: BW of outcome distributions and the fidelity F → FuchsVdGraaf.bhattacharyya of outcomeDist, and QAlgorithms.rootFidelity = Re Tr √(√ρ0 ρ1 √ρ0); reason: same quantities; F is not squared, as the identification with min BW requires
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.8

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_MayersBC_outcomeDist
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.8: "Furthermore, in [7,18] it is shown that
the minimum of BW over all possible measurement is the fidelity F between ρ0 and ρ1." For
density matrices `ρ_0, ρ_1`: (1) every measurement `{M_j}` (any finite outcome set) has
`F(ρ_0, ρ_1) ≤ BW(p_0, p_1)` for its outcome distributions `p_b(j) = Tr(M_j ρ_b)`, and (2) some
measurement attains `BW(p_0, p_1) = F(ρ_0, ρ_1)`. Here `F = Tr √(√ρ_0 ρ_1 √ρ_0)`.

**Formalization Note.** `F` is the published `QAlgorithms.rootFidelity` (not squared), which is
the value the minimum of `BW` takes. `BW` is the published `FuchsVdGraaf.bhattacharyya`.
Measurements are POVMs; the attaining one has outcomes `Fin m` for some `m`. Both halves of
"minimum" (lower bound and attainment) are stated. -/
theorem fuchs_caves {ι : Type} [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ)
    (h0 : IsDensityMatrix ρ0) (h1 : IsDensityMatrix ρ1) :
    (∀ {J : Type} [Fintype J] (M : J → Matrix ι ι ℂ), IsPOVM M →
        rootFidelity ρ0 ρ1 ≤ FuchsVdGraaf.bhattacharyya (outcomeDist M ρ0) (outcomeDist M ρ1)) ∧
      ∃ (m : ℕ) (M : Fin m → Matrix ι ι ℂ), IsPOVM M ∧
        FuchsVdGraaf.bhattacharyya (outcomeDist M ρ0) (outcomeDist M ρ1) = rootFidelity ρ0 ρ1 := by sorry

end MayersBC
