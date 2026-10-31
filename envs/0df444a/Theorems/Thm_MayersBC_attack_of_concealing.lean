-- Prove2me | Theorems.Thm_MayersBC_attack_of_concealing
-- name    : MayersBC.attack_of_concealing
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:58:13.856082+00:00
-- url     : https://prove2.me/theorems/9327a780-8c83-4406-ad1f-776da82583a9
-- title:
--   Sections b and d, pp.5–9 — if a pure-state commitment conceals the bit, Alice opens $0$ honestly and $1$ with probability $\ge$ honest $-\,4\sqrt\varepsilon$
-- statement:
--   Consider any commitment scheme in which Alice commits to $b$ by sending Bob a pure state $\psi_w$ chosen with probability $p_b(w)$ ($p_0, p_1$ probability distributions on a finite set $W$, each $\psi_w$ a unit vector), Bob measures with a POVM $\{E_y\}$, and Bob accepts an opening $w$ of $b$ when a test $T_b(w, y)$ returns ok. Let
--
--   $$
--   \rho_b = \sum_w p_b(w)\, |\psi_w\rangle\langle\psi_w| ,
--   $$
--
--   and suppose Bob's criterion holds: every binary guess between $\rho_0$ and $\rho_1$ has $|\mathrm{PE} - \tfrac12| \le \varepsilon$. Then Alice can prepare **one** pure state $\varphi$ of her register $\mathbb C^W$ and Bob's system, whose reduced state on Bob's side is $\rho_0$, and there are measurements $N_0, N_1$ on her register alone such that
--
--   1. opening $0$ with $N_0$ is accepted with exactly the honest probability $\Pr(T_0(W^{(0)}) = ok)$;
--   2. opening $1$ with $N_1$ is accepted with probability at least
--   $$
--   \Pr\big(T_1(W^{(1)}) = ok\big) - 4\sqrt{\varepsilon} .
--   $$
--
--   So a commitment that is secure against Bob in this sense is not binding: Alice decides the bit after the commit phase.
--
--   Differences from the source:
--   - generalization: the BCJL commitment (BB84 product states, the coset distribution, Bob's random-basis measurement) → any finite mixture of pure states {p_b(w), ψ_w}, any Bob POVM E and any test T; reason: the argument of pp.7–9 uses none of the BCJL specifics (p.3: one need not understand the protocol in detail); BCJL is the instance proved in bcjl_insecure
--   - generalization: ε = 1/25 → any real ε; reason: the argument uses no property of the value
--   - reading: Bob's best guess X satisfies |PE − 1/2| ≤ ε → IsConcealing ε ρ0 ρ1 (every binary guess); reason: equivalent, as in IsConcealing
--   - encoding: Alice's system A, measurements M_b^(A), and 'Alice measures after Bob' (the measurements commute) → Alice's register ℂ^W as the first tensor factor, POVMs N_0, N_1 indexed by W, and the joint probability ⟨φ|N_w ⊗ E_y|φ⟩ (cheatAccept); reason: the outcome law of commuting measurements on different systems does not depend on their order; a register of dimension |W| purifies ρ_0 and ρ_1
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section b, pp.5–6, and section d, pp.7–9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_MayersBC_mixtureDensity
import Definitions.Def_MayersBC_IsConcealing
import Definitions.Def_MayersBC_honestAccept
import Definitions.Def_MayersBC_cheatAccept
open QAlgorithms

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, sections b and d, pp.5–9: "In the remainder of this paper,
we show that for all practical purposes, if the protocol is secure against Bob, then the above
condition holds" (p.5–6), carried out on pp.7–9 for any commitment in which Alice commits to `b`
by sending a pure state `ψ_w` drawn with probability `p_b(w)`.

Let `p_0, p_1` be probability distributions on a finite set `W`, `ψ_w` unit vectors of the
photon space, `E` Bob's measurement (outcomes `Y`), and `T_b(w, y)` any test. If Bob's criterion
holds, `|PE − ½| ≤ ε` for every guess between `ρ_0 = Σ_w p_0(w)|ψ_w⟩⟨ψ_w|` and
`ρ_1 = Σ_w p_1(w)|ψ_w⟩⟨ψ_w|`, then Alice can prepare **one** unit vector `φ` of `ℂ^W ⊗ photons`
whose reduced state on the photons is `ρ_0`, and there are measurements `N_0, N_1` on her register
alone such that opening `0` with `N_0` is accepted with exactly the honest probability, and
opening `1` with `N_1` is accepted with probability at least the honest one minus `4√ε`.

**Formalization Note.** Alice's system is the register `ℂ^W` (first tensor factor), and her
announced `w` is the outcome of `N_b`; acceptance probabilities are `honestAccept` and
`cheatAccept`. Bob's measurement and the test are arbitrary; nothing about BCJL is assumed. -/
theorem attack_of_concealing {W Y ι : Type} [Fintype W] [DecidableEq W] [Fintype Y]
    [Fintype ι] [DecidableEq ι] (p : ZMod 2 → W → ℝ) (hp : ∀ b, FuchsVdGraaf.IsProbDist (p b))
    (ψ : W → EuclideanSpace ℂ ι) (hψ : ∀ w, IsState (ψ w)) (E : Y → Matrix ι ι ℂ)
    (hE : IsPOVM E) (T : ZMod 2 → W → Y → Prop) (ε : ℝ)
    (hBob : IsConcealing ε (mixtureDensity (p 0) ψ) (mixtureDensity (p 1) ψ)) :
    ∃ φ : EuclideanSpace ℂ (W × ι), IsState φ ∧
      traceLeft (pureDensity φ) = mixtureDensity (p 0) ψ ∧
      ∃ N0 N1 : W → Matrix W W ℂ, IsPOVM N0 ∧ IsPOVM N1 ∧
        cheatAccept φ N0 E T 0 = honestAccept p ψ E T 0 ∧
        honestAccept p ψ E T 1 - 4 * Real.sqrt ε ≤ cheatAccept φ N1 E T 1 := by sorry

end MayersBC
