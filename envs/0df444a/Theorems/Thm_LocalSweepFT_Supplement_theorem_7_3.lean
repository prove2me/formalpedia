-- Prove2me | Theorems.Thm_LocalSweepFT_Supplement_theorem_7_3
-- name    : LocalSweepFT.Supplement.theorem_7_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:35:10.987993+00:00
-- url     : https://prove2.me/theorems/83a1f850-2b21-4050-8b1e-babfae0ba9a6
-- title:
--   Theorem 7.3 (operator-requested pinned-down version) — $n^{d+1}$ noiseless sweep cycles decode a local stochastic Pauli error except w.p. $\le A\,n^k p^{cn}$
-- statement:
--   This is the operator-requested pinned-down version of Theorem 7.3, stated in the same pinned-down model as the mission's goal: the noise is a single layer of local stochastic Pauli errors on the qubits, the decoder is any pair of sweep rules, and success means exact recovery of $|\psi\rangle\langle\psi|$.
--
--   Let $d,d'$ be integers with $d'\ge2$ and $d-d'\ge2$. There are constants $p_0\in(0,1)$, $A>0$, $c>0$ and $k\in\mathbb N$, depending only on $d$ and $d'$, such that the following holds for every side length $n\ge1$:
--
--   1. for every pair of sweep rules $r_1$ (sector $d'$) and $r_2$ (sector $d-d'$),
--   2. for every codeword $|\psi\rangle$ of the side-$n$ $(d,d')$-Toric code,
--   3. for every $p\in(0,p_0)$ and every distribution $\nu$ of Pauli error patterns $E$ on the register's qubits that is local stochastic with rate $p$,
--
--   $$\Pr_{E\sim\nu}\Big[\mathcal S^{\,n^{d+1}}\big(P_E|\psi\rangle\langle\psi|P_E^\dagger\big)\ne|\psi\rangle\langle\psi|\Big]\le A\,n^k\,p^{cn},$$
--
--   where $\mathcal S$ is the channel of one sweep cycle with the rules $r_1,r_2$ and $P_E$ is the Pauli error of $E$.
--
--   So the sweep rule, which in the threshold theorem only restrains errors, is also a decoder: with no faults during decoding, $n^{d+1}$ cycles (the number of vertices times the side length) remove a correlated local stochastic error of rate below the threshold with probability at least $1-O(\mathrm{poly}(n))\,p^{\Omega(n)}$.
--
--   **Formalization Note** The sweep rules, codewords and the sweep cycle are the mission's published definitions (`LocalSweepFT.IsSweepRule` on `ZMod n`, `LocalSweepFT.codeSpace`, `LocalSweepFT.sweepCycleKraus`); the error model and the failure probability are `LocalSweepFT.Supplement.idealDecodeFailProb`. The power $p^{cn}$ is the real power.
--
--   Differences from the source:
--   - reading: p₀ chosen first, for fixed d, d′ → ∀ d d′ (with d′ ≥ 2, d − d′ ≥ 2) ∃ p₀ A c k; reason: the constants of the proof (through Lemma 6.2 and Corollary 5.11) depend on d, d′, and the informal version (p.5) reads "Fix d, d′ with d′, d − d′ ≥ 2. There is a constant p0 > 0"
--   - reading: probability at least 1 − O(poly(n)) p^{Ω(n)} → failure probability ≤ A·n^k·p^{c·n} for every n ≥ 1, with A, c > 0 and k ∈ ℕ fixed before n; reason: the standard reading of O(poly(n)) and Ω(n), the same pin as the mission's goal; finitely many small n are absorbed into A and c because the zero error never fails and every failing error has a non-identity Pauli
--   - reading: the sweep cycles (with "the" sweep rule) → every pair of sweep rules rule₁ : LocalRule d d′, rule₂ : LocalRule d (d − d′) satisfying LocalSweepFT.IsSweepRule (ZMod n); reason: Def 4.6 does not fix which admissible chain is flipped; the statement holds for every admissible choice, as in the mission's goal
--   - reading: a local stochastic noise channel N_E with rate p applied to |ψ⟩⟨ψ| → a PMF on Pauli error patterns E of the register's qubits with Pr[E(q) ≠ (0,0) for all q ∈ S] ≤ p^{|S|} for every finite S, and ρ_E = P_E|ψ⟩⟨ψ|P_E†; reason: Def 3.7 (p.14) with Pauli faults, and the locations of the single initial fault layer of Claim 7.2's proof (p.62)
--   - reading: results in |ψ⟩ with probability at least → the ν-probability of the event that the n^{d+1}-fold iterated sweep-cycle channel maps P_E|ψ⟩⟨ψ|P_E† to an operator other than |ψ⟩⟨ψ| is the failure probability; reason: P_E|ψ⟩ has a definite syndrome, so each cycle maps it to a pure state and recovery of |ψ⟩ is exact equality with |ψ⟩⟨ψ|
--   - encoding: a codeword |ψ⟩ (a unit vector) → any vector ψ of LocalSweepFT.codeSpace d d′ n, not necessarily normalized; reason: rescaling ψ rescales both operators of the event by the same factor, and ψ = 0 gives the empty event, so the instances are the same
--   - encoding: p ∈ (0, 1) of Def 3.7 → 0 < p < p₀ with p₀ < 1; reason: Def 3.7 takes p ∈ (0, 1)
-- source:
--   Ponarovsky, Local Quantum Fault Tolerance Without Expansion, arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5bbb5cb9a66ee05f2fa2953fc49add2665da350a30afceb79503cca41), Theorem 7.3, p.62 (proof p.62; informal version p.5); Definition 3.7, p.14; Claim 7.2, pp.61–62

import Mathlib
import Definitions.Def_LocalSweepFT_encMat
import Definitions.Def_LocalSweepFT_IsSweepRule
import Definitions.Def_LocalSweepFT_sweepCycleKraus
import Definitions.Def_LocalSweepFT_Supplement_idealDecodeFailProb

namespace LocalSweepFT.Supplement

/-- Theorem 7.3, p.62 (Ponarovsky, *Local Quantum Fault Tolerance Without Expansion*,
arXiv:2610.38847 (version of November 3, 2026, sha256 85723eb5…)), operator-requested pinned-down
version: "There exists a constant p0 ∈ (0, 1) such that for any local stochastic noise channel NE
with rate p < p0, and a quantum state ρ = NE(|ψ⟩⟨ψ|), where |ψ⟩ is a codeword of the (d, d′)-Toric
code satisfying d′, d − d′ ≥ 2, the application of n^{d+1} (ideal) sweep-cycles on ρ results in |ψ⟩
with probability at least 1 − O(poly(n)) p^{Ω(n)}."

For all `d, d′` with `d′ ≥ 2` and `d − d′ ≥ 2` there are constants `p₀ ∈ (0, 1)`, `A, c > 0` and
`k ∈ ℕ` (depending only on `d, d′`) such that for every side length `n ≥ 1`, every pair of sweep rules
`rule₁` (sector `d′`) and `rule₂` (sector `d − d′`), every codeword `ψ` of the side-`n`
`(d, d′)`-Toric code, every `p ∈ (0, p₀)` and every local stochastic distribution `ν` of rate `p` of
Pauli errors on the register's qubits, the probability that `n^{d+1}` noiseless sweep cycles applied
to `P_E |ψ⟩⟨ψ| P_E†` do not return exactly `|ψ⟩⟨ψ|` is at most `A · n^k · p^{c n}`.

**Formalization Note.** The constants are chosen after `d, d′` (as in Lemma 6.2 and the informal
version, p.5: "Fix d, d′ … There is a constant p0"); `O(poly(n)) p^{Ω(n)}` is pinned as
`A · n^k · p^{c n}` for all `n ≥ 1` (real power `p ^ (c * n)`); every pair of sweep rules is allowed
(`LocalSweepFT.IsSweepRule` on `ZMod n`); the noise is a single Pauli fault layer on the qubits before
the noiseless cycles (Def 3.7 with the initial fault layer of Claim 7.2, p.62); "results in `|ψ⟩`" is
exact equality with `|ψ⟩⟨ψ|`; a codeword is any vector of `LocalSweepFT.codeSpace d d′ n`. -/
theorem theorem_7_3 (d d' : ℕ) (h1 : 2 ≤ d') (h2 : 2 ≤ d - d') :
    ∃ p₀ : ℝ, 0 < p₀ ∧ p₀ < 1 ∧ ∃ A c : ℝ, 0 < A ∧ 0 < c ∧ ∃ k : ℕ,
      ∀ (n : ℕ) [NeZero n] (rule₁ : LocalRule d d') (rule₂ : LocalRule d (d - d')),
        IsSweepRule (ZMod n) rule₁ → IsSweepRule (ZMod n) rule₂ →
        ∀ ψ ∈ codeSpace d d' n, ∀ p : ℝ, 0 < p → p < p₀ →
          ∀ ν : PMF (QCell d d' n → ZMod 2 × ZMod 2), IsRegLocalStochastic ν p →
            idealDecodeFailProb (by omega) rule₁ rule₂ ψ ν ≤
              ENNReal.ofReal (A * (n : ℝ) ^ k * p ^ (c * n)) := by sorry

end LocalSweepFT.Supplement
