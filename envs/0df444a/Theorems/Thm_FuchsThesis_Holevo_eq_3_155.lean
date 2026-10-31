-- Prove2me | Theorems.Thm_FuchsThesis_Holevo_eq_3_155
-- name    : FuchsThesis.Holevo.eq_3_155
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:15.006548+00:00
-- url     : https://prove2.me/theorems/acd15b60-d7ed-4333-8a0a-73eef3dd68c2
-- title:
--   Eq. (3.155): $J(0)=J(1)=S(0)=S(1)=0$
-- statement:
--   Let $\hat\rho_0,\hat\rho_1$ be density operators on a finite-dimensional Hilbert space, and let $\{\hat E_b\}$ be any POVM with finitely many outcomes. Let $J(t)$ be the mutual information (3.144) of the binary channel with priors $1-t,t$ with respect to $\{\hat E_b\}$, and $S(t)=S(\hat\rho)-(1-t)S(\hat\rho_0)-tS(\hat\rho_1)$ the Holevo quantity (3.149). Then
--
--   $$
--   J(0)=J(1)=S(0)=S(1)=0 .
--   $$
--
--   These boundary values are what turn the curvature comparison $S''\le L''\le J''$ into the bounds $I(t)\le L(t)\le S(t)$.
--
--   Differences from the source:
--   - encoding: density operators on a D-dimensional Hilbert space → complex matrices over an arbitrary finite index type d with WildeQIT.IsDensityOperator; reason: Lean convention; the same states
--   - encoding: a measurement {Ê_b} with finitely many outcomes → a family E : Fin m → Matrix d d ℂ for any m, with FuchsVdGraaf.IsPOVM E; reason: Lean convention; the same measurements
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, eq. (3.155), p.67 (PDF p.76)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_FuchsVdGraaf_IsPOVM
import Definitions.Def_FuchsThesis_Holevo_mutualInfo
import Definitions.Def_FuchsThesis_Holevo_holevoS

namespace FuchsThesis.Holevo

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, eq. (3.155), p.67 (PDF p.76): for density operators `ρ̂0, ρ̂1` on a
finite-dimensional space and every POVM `{Ê_b}`,
`J(0) = J(1) = S(0) = S(1) = 0`.

**Formalization Note.** `J` is `mutualInfo` (3.144) and `S` is `holevoS` (3.149), both in nats;
the POVM has any finite number `m` of outcomes. -/
theorem eq_3_155 {d : Type} [Fintype d] [DecidableEq d] (ρ0 ρ1 : Matrix d d ℂ)
    (h0 : WildeQIT.IsDensityOperator ρ0) (h1 : WildeQIT.IsDensityOperator ρ1)
    {m : ℕ} (E : Fin m → Matrix d d ℂ) (hE : FuchsVdGraaf.IsPOVM E) :
    mutualInfo ρ0 ρ1 E 0 = 0 ∧ mutualInfo ρ0 ρ1 E 1 = 0 ∧
      holevoS ρ0 ρ1 0 = 0 ∧ holevoS ρ0 ρ1 1 = 0 := by sorry

end FuchsThesis.Holevo
