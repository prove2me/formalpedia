-- Prove2me | Theorems.Thm_MayersBC_hjw_steering
-- name    : MayersBC.hjw_steering
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:52.586967+00:00
-- url     : https://prove2.me/theorems/be7b2928-17cb-4ecb-9c42-7fe103c6676a
-- title:
--   Section c, p.6 — Hughston–Jozsa–Wootters: Alice's measurement on $A$ realizes any mixture of $\rho$
-- statement:
--   Let $\varphi$ be a vector of $A \otimes \mathcal H$ (Alice's system first, $\mathcal H$ the photon space) whose reduced state on the photons is the density operator of a mixture,
--
--   $$
--   \operatorname{Tr}_A |\varphi\rangle\langle\varphi| = \rho = \sum_{w \in W} p_w\, |\psi_w\rangle\langle\psi_w| ,
--   $$
--
--   where $p$ is a probability distribution on a finite set $W$ and each $\psi_w$ is a unit vector. Then there is a measurement $\{N_w\}_{w\in W}$ on $A$ alone such that for every $w$
--
--   $$
--   \operatorname{Tr}_A\big[(N_w \otimes I)\,|\varphi\rangle\langle\varphi|\big] = p_w\, |\psi_w\rangle\langle\psi_w| .
--   $$
--
--   The left side is the unnormalized state of the photons after Alice obtains $w$: its trace $p_w$ is the probability of $w$, and given $w$ the photons are in $|\psi_w\rangle$. So by measuring $A$, Alice realizes any mixture of $\rho$ she chooses, after the photons have left.
--
--   Differences from the source:
--   - encoding: Alice receives the classical outcome ψ with probability p(ψ), and ψ determines the collapsed state |ψ⟩ on Bob's side → a POVM N on A with Tr_A[(N_w ⊗ I)|φ⟩⟨φ|] = p_w |ψ_w⟩⟨ψ_w| for every w; reason: the unnormalized post-measurement state records both the probability and the collapse
--   - reading: a mixture {(|ψ⟩, p(ψ)} with Σ_c p(ψ)|ψ⟩⟨ψ| = ρ, the outcome labelled by the state ψ → a mixture indexed by a finite set W, ρ = Σ_w p_w |ψ_w⟩⟨ψ_w|, the outcome labelled by w; reason: the printed summation index c is a slip for the mixture's index; labelling outcomes by w also allows two labels with the same state
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section c, p.6 (used in section b, p.5, and section d, p.9)

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_MayersBC_mixtureDensity
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section c, p.6 (used in sections b and d, pp.5, 9): "It is
shown in [8] that by choosing the appropriate measurement on A, Alice may choose any mixture
{(|ψ⟩, p(ψ)} such that Σ p(ψ)|ψ⟩⟨ψ| = ρ. … when Alice chooses the mixture {(|ψ⟩, p(ψ)}, she
receives the classical outcome ψ with probability p(ψ) and, furthermore, the classical
information ψ received by Alice uniquely determines the collapsed state |ψ⟩ of the n photons on
Bob's side." Let `φ` be a vector of `A ⊗ ℂ^ι` (Alice's system first) whose reduced state on the
photons is `ρ = Σ_w p_w |ψ_w⟩⟨ψ_w|`, for a probability distribution `p` and unit vectors `ψ_w`.
Then there is a measurement `{N_w}` on `A` alone such that, for every outcome `w`,
`Tr_A[(N_w ⊗ I)|φ⟩⟨φ|] = p_w |ψ_w⟩⟨ψ_w|`: outcome `w` occurs with probability `p_w` and leaves the
photons in `|ψ_w⟩`.

**Formalization Note.** The measurement is a POVM indexed by the ensemble's index set `W`; `A` is
any finite system (no dimension condition). `φ` is a unit vector automatically (its reduced state
has trace one). Alice's register is the first factor of `traceLeft`. -/
theorem hjw_steering {A W ι : Type} [Fintype A] [DecidableEq A] [Fintype W] [Fintype ι]
    [DecidableEq ι] (p : W → ℝ) (hp : FuchsVdGraaf.IsProbDist p) (ψ : W → EuclideanSpace ℂ ι)
    (hψ : ∀ w, IsState (ψ w)) (φ : EuclideanSpace ℂ (A × ι))
    (hmarg : traceLeft (pureDensity φ) = mixtureDensity p ψ) :
    ∃ N : W → Matrix A A ℂ, IsPOVM N ∧
      ∀ w, traceLeft (Matrix.kronecker (N w) (1 : Matrix ι ι ℂ) * pureDensity φ) =
        ((p w : ℝ) : ℂ) • pureDensity (ψ w) := by sorry

end MayersBC
