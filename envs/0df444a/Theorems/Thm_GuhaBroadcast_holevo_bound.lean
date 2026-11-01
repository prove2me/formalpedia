-- Prove2me | Theorems.Thm_GuhaBroadcast_holevo_bound
-- name    : GuhaBroadcast.holevo_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:48.6626+00:00
-- url     : https://prove2.me/theorems/a10d2fcb-73eb-43c0-82d8-680fa0885e8b
-- title:
--   Holevo's bound on the full Fock space (footnote 3)
-- statement:
--   Let $X$ be a finite alphabet with prior $(p_x)$, let $\hat\rho_x$ be states of $n$ bosonic modes (on the full Fock space, no photon cutoff), and let $\{\Pi_y\}_{y\in Y}$ be a POVM with finitely many outcomes. Let $Y$ be the measurement outcome, so that the joint law is $P(x,y)=p_x\operatorname{Tr}(\hat\rho_x\Pi_y)$. If $S\big(\sum_x p_x\hat\rho_x\big)<\infty$, then
--
--   $$
--   I(X;Y)\le\chi(p_x,\hat\rho_x)=S\Big(\sum_x p_x\hat\rho_x\Big)-\sum_x p_xS(\hat\rho_x).
--   $$
--
--   This is the cited result the paper uses in the third line of (14) and the second line of (15) to pass from the classical decoding statistics to a quantum entropy quantity.
--
--   **Formalization Note** States are the published `State (NumberString n)`, the POVM is `FockPOVM` with a finite outcome type, $\operatorname{Tr}(\hat\rho\Pi)$ is `realFockTracePair`, entropies are in nats.
--
--   Differences from the source:
--   - reading: 'X the input alphabet', 'Y the resulting output (classical) alphabet' (footnote 3) → finite types X and Y (finite-outcome POVM); reason: the paper's alphabets have sizes (footnote 1, p.1) and the bound is applied to finite message sets
--   - encoding: χ(p_i, ρ̂_i) given by (3) as a real number → hypothesis S(Σ p_x ρ̂_x) < ∞, χ formed with toReal; reason: this is exactly when (3) is a real number; if S(Σ p_x ρ̂_x) = ∞ the paper's bound is trivial
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, footnote 3, p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_holevo
import Definitions.Def_GuhaBroadcast_mutualInfo

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, footnote 3, p.3 (PDF page; the paper prints no page numbers): "Holevo's bound
[10]: Let X be the input alphabet for a channel, {p_i, ρ̂_i} the priors and modulating states, {Π_j}
be a POVM, and Y the resulting output (classical) alphabet. The Shannon mutual information I(X; Y) is
upper bounded by the Holevo information χ(p_i, ρ̂_i)".

Here the states live on the full n-mode Fock space, the alphabet `X` is finite, the POVM has finitely
many outcomes `Y`, and the joint law of `(X, Y)` is `P(x, y) = p_x Tr(ρ̂_x Π_y)`, with `E` the POVM `{Π_y}`.

**Formalization Note.** Cited by the paper, stated here in the mission's Fock-space encoding because no
such version exists on the platform. The hypothesis `S(Σ_x p_x ρ̂_x) < ∞` is what makes the paper's
formula (3) a real number (it forces `S(ρ̂_x) < ∞` whenever `p_x > 0`); with it `holevo` is exactly
`χ`. Nats; `Tr(ρ̂ Π)` is the published `realFockTracePair`. -/
theorem holevo_bound {n : ℕ} {X Y : Type} [Fintype X] [Fintype Y]
    (p : X → ℝ) (hp : ∀ x, 0 ≤ p x) (hp1 : ∑ x, p x = 1)
    (ρ : X → State (NumberString n)) (E : FockPOVM (NumberString n) Y)
    (hfin : spectralEntropyNats (mixture p (fun x => (ρ x).coefficients)) ≠ ⊤) :
    mutualInfo (fun x y => p x * realFockTracePair (ρ x).coefficients (E.effect y)) ≤
      holevo p (fun x => (ρ x).coefficients) := by sorry

end GuhaBroadcast
