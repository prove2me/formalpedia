-- Prove2me | Theorems.Thm_MayersBC_exists_unitary_inner_eq_rootFidelity
-- name    : MayersBC.exists_unitary_inner_eq_rootFidelity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:35.040532+00:00
-- url     : https://prove2.me/theorems/385767fa-a692-4974-8459-0a14ad6ab73b
-- title:
--   Section d, p.8 — purifications with $\langle\varphi_0|\varphi_1\rangle = F \ge 1 - 2\varepsilon$ (corrected: $\langle\varphi_0|\varphi_1\rangle = F$, not $\langle\varphi_0|\varphi_1\rangle^2 = F$)
-- statement:
--   Let $A$ be a finite-dimensional system (Alice's) and let $\psi_0, \psi_1$ be unit vectors of $A \otimes \mathcal H$, where $\mathcal H$ is the photon space, whose reduced states on the photons are $\rho_0 = \operatorname{Tr}_A|\psi_0\rangle\langle\psi_0|$ and $\rho_1 = \operatorname{Tr}_A|\psi_1\rangle\langle\psi_1|$. Suppose $\rho_0, \rho_1$ satisfy Bob's criterion with parameter $\varepsilon$. Then there is a unitary $U$ on $A$ such that the purifications $\varphi_0 = (U \otimes I)\psi_0$ of $\rho_0$ and $\varphi_1 = \psi_1$ of $\rho_1$ satisfy
--
--   $$
--   \langle \varphi_0 | \varphi_1 \rangle = F(\rho_0, \rho_1) \ge 1 - 2\varepsilon ,
--   $$
--
--   where $F = \operatorname{Tr}\sqrt{\sqrt{\rho_0}\,\rho_1\sqrt{\rho_0}}$; in particular the overlap is real and nonnegative. This is the form of Uhlmann's theorem the attack uses.
--
--   Differences from the source:
--   - correction: ⟨φ0|φ1⟩² = F → ⟨φ0|φ1⟩ = F; reason: with F the minimum of BW (the root fidelity, as on the page), the attained overlap is F; the printed square is false: for ρ0 = |0⟩⟨0| and ρ1 = |+⟩⟨+| on ℂ², every pair of purifications has |⟨φ0|φ1⟩|² ≤ |⟨0|+⟩|² = 1/2, while F = min BW = 1/√2 (the computational-basis measurement gives BW = 1/√2), so ⟨φ0|φ1⟩² = F is impossible
--   - generalization: there exist two purifications φ0 and φ1 of ρ0 and ρ1 → for any purifications ψ0, ψ1 on the same space A ⊗ photons, φ0 = (U ⊗ I)ψ0 and φ1 = ψ1 for some unitary U on A; reason: fixing the purifying space and the purifications in advance is stronger; applied to any one pair of purifications (one always exists) it gives the page's existence claim
--   - reading: F ≥ (1 − 2ε), with ε from Bob's criterion on the best guess → 1 − 2ε ≤ rootFidelity ρ0 ρ1 under IsConcealing ε ρ0 ρ1; reason: same equivalence of the best guess with every binary guess as in IsConcealing
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.8 (display after Uhlmann's theorem)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_QuantumInformation
import Definitions.Def_MayersBC_IsConcealing
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.8 (display after Uhlmann's theorem):
"Therefore, there exists two purifications φ0 and φ1 such that ⟨φ0|φ1⟩² = F ≥ (1 − 2ε)",
corrected to `⟨φ_0|φ_1⟩ = F ≥ (1 − 2ε)`. Let `ψ_0, ψ_1` be unit vectors of `A ⊗ ℂ^ι` (Alice's
system first) whose reduced states on the photons are `ρ_0` and `ρ_1`, and let `ρ_0, ρ_1` satisfy
Bob's criterion with `ε`. Then there is a unitary `U` on `A` such that the purification
`φ_0 = (U ⊗ I)ψ_0` of `ρ_0` and `φ_1 = ψ_1` of `ρ_1` have `⟨φ_0|φ_1⟩ = F(ρ_0, ρ_1)` (a real,
nonnegative number), and `F(ρ_0, ρ_1) ≥ 1 − 2ε`.

**Formalization Note.** `F` is the published `QAlgorithms.rootFidelity` `Tr √(√ρ_0 ρ_1 √ρ_0)`,
the minimum of `BW` (p.8). With this `F` the attained overlap is `F`, not `√F`: the printed
square is false (for `ρ_0 = |0⟩⟨0|`, `ρ_1 = |+⟩⟨+|` every pair of purifications has
`|⟨φ_0|φ_1⟩|² ≤ 1/2 < F = 1/√2`). `inner ℂ x y` is `⟨x|y⟩`, conjugate-linear in `x`; `act` applies a
matrix to a vector. The purifying space `A` and the first purifications are fixed in advance,
which is stronger than "there exist two purifications". Bob's criterion is used only for the
clause `F ≥ 1 − 2ε`; it holds for every pair of density matrices at `ε = 1/2`. -/
theorem exists_unitary_inner_eq_rootFidelity {A ι : Type} [Fintype A] [DecidableEq A]
    [Fintype ι] [DecidableEq ι] (ρ0 ρ1 : Matrix ι ι ℂ) (ψ0 ψ1 : EuclideanSpace ℂ (A × ι))
    (hψ0 : IsState ψ0) (hψ1 : IsState ψ1)
    (hp0 : traceLeft (pureDensity ψ0) = ρ0) (hp1 : traceLeft (pureDensity ψ1) = ρ1) (ε : ℝ)
    (hc : IsConcealing ε ρ0 ρ1) :
    (∃ U ∈ Matrix.unitaryGroup A ℂ,
      inner ℂ (act (Matrix.kronecker U (1 : Matrix ι ι ℂ)) ψ0) ψ1 = ((rootFidelity ρ0 ρ1 : ℝ) : ℂ)) ∧
      1 - 2 * ε ≤ rootFidelity ρ0 ρ1 := by sorry

end MayersBC
