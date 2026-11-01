-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_23
-- name    : GuhaBroadcast.eq_23
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:32.204112+00:00
-- url     : https://prove2.me/theorems/1e7cc420-6b8c-46ae-a7a6-df1c7e7424a7
-- title:
--   Eq. (23): average entropy at Charlie is at least $n\,g((1-\eta)\beta\bar N)$
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Let $\beta\in[0,1]$ satisfy $\frac1{M_C}\sum_kS(\hat\rho^{B^n}_k)=n\,g(\eta\beta\bar N)$, as in (20). Then
--
--   $$
--   \sum_k p_{W_C}(k)\,S\big(\hat\rho^{C^n}_k\big)\ge n\,g\big((1-\eta)\beta\bar N\big).
--   $$
--
--   It combines (18) summed over $k$ with (22).
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - generalization: derived assuming Strong conjecture 2 (p.3, before (18)) → no conjecture hypothesis; reason: the conjecture is used only on finite-energy codewords, where the Proved entropy photon-number inequality (OAI.EntropyPhotonNumber.entropy_photon_number_inequality, e96b6eda) supplies it; the conditional statement follows
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (23), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_charlieOutput
import Definitions.Def_GuhaBroadcast_bobCodeword
import Definitions.Def_GuhaBroadcast_charlieCodeword

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (23), p.4 (PDF page; the paper prints no page numbers): "From Eq. (22), and
Eq. (18) summed over k, we then obtain Σ_k p_{W_C}(k)S(ρ̂_k^{Cⁿ}) ≥ ng((1 − η)β N̄)."

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).
`β` is that of (20): `β ∈ [0,1]` with `Σ_k p_{W_C}(k) S(ρ̂_k^{Bⁿ}) = n g(ηβN̄)`.

**Formalization Note.** Uniform prior `p_{W_C}(k) = 1/M_C`. Entropies are converted with `toReal`; under
the budget they are finite, and with an infinite entropy read as `0` the inequality would only be harder.
No conjecture is assumed (the page's (18) rests on Strong conjecture 2; see `eq_18`). -/
theorem eq_23 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar))
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ : (∑ k, (spectralEntropyNats (bobCodeword eta C k)).toReal) / (MC : ℝ) =
      (n : ℝ) * g (eta * β * Nbar)) :
    (n : ℝ) * g ((1 - eta) * β * Nbar) ≤
      (∑ k, (spectralEntropyNats (charlieCodeword eta C k)).toReal) / (MC : ℝ) := by sorry

end GuhaBroadcast
