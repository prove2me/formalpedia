-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_18
-- name    : GuhaBroadcast.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:27:35.187797+00:00
-- url     : https://prove2.me/theorems/3d58dd12-05f7-4766-a880-6b2c7b2929be
-- title:
--   Eq. (18): $S(\hat\rho^{C^n}_k)\ge n\,g((1-\eta)\beta_k\bar N_k)$, with no conjecture assumed
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Let $k$ be a message of Charlie and $\beta_k\in[0,1]$ with $S(\hat\rho^{B^n}_k)=n\,g(\eta\beta_k\bar N_k)$, as in (17). Then
--
--   $$
--   S\big(\hat\rho^{C^n}_k\big)\ge n\,g\big((1-\eta)\beta_k\bar N_k\big).
--   $$
--
--   Charlie's state is Bob's state sent through a further beam splitter of transmissivity $\eta'=(1-\eta)/\eta$ with vacuum on the other port; (18) is the resulting minimum-output-entropy bound. It is the only step of the converse where the paper assumes Strong conjecture 2; here no conjecture is assumed, since the codewords have finite energy and the entropy photon-number inequality is Proved on the platform for finite-energy inputs.
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - generalization: derived assuming Strong conjecture 2 (p.3, before (18)) → no conjecture hypothesis; reason: the conjecture is used only on finite-energy codewords, where the Proved entropy photon-number inequality (OAI.EntropyPhotonNumber.entropy_photon_number_inequality, e96b6eda) supplies it; the conditional statement follows
--   - reading: N̄_{k_j} = 'the mean photon number of the jth symbol ρ̂_k^{B_j}' (p.3) → the input mean photon number of mode j of the k-th codeword, averaged over m (Bob's mode then has mean ηN̄_{k_j}); reason: (16) evaluates g(ηN̄_{k_j}), which bounds Bob's mode only when N̄_{k_j} is measured at the input
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (18), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_charlieOutput
import Definitions.Def_GuhaBroadcast_bobCodeword
import Definitions.Def_GuhaBroadcast_charlieCodeword
import Definitions.Def_GuhaBroadcast_modeMeanPhotons
import Definitions.Def_GuhaBroadcast_codewordMeanPhotons

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (18), p.3 (PDF page; the paper prints no page numbers): "Because of the
degraded nature of the channel, Charlie's state can be obtained as the output of a beam splitter whose
input states are Bob's state (coupling coefficient η′ = (1 − η)/η to Charlie) and a vacuum state
(coupling coefficient 1 − η′ to Charlie). It follows, from assuming the truth of Strong conjecture 2
(see Appendix), that S(ρ̂_k^{Cⁿ}) ≥ ng((1 − η)β_kN̄_k)."

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).
`β_k ∈ [0,1]` is any number with `S(ρ̂_k^{Bⁿ}) = n g(η β_k N̄_k)`, as produced by (17).

**Formalization Note.** **No conjecture is assumed.** The page derives (18) from Strong conjecture 2,
which it applies only to the codeword `ρ̂_k^{Bⁿ}`, a state of finite mean energy under the budget. That
finite-energy case follows from the entropy photon-number inequality, Proved on the platform
(`OAI.EntropyPhotonNumber.entropy_photon_number_inequality`, e96b6eda-42d9-4886-afaa-616a4ea529c2), applied
with a vacuum input; the mission states (18) unconditionally. Connecting the two Fock-space encodings is
proof work. Entropies in `ℝ≥0∞`, nats. -/
theorem eq_18 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar)) (k : Fin MC) (βk : ℝ) (hβk0 : 0 ≤ βk) (hβk1 : βk ≤ 1)
    (hβk : spectralEntropyNats (bobCodeword eta C k) =
      ENNReal.ofReal ((n : ℝ) * g (eta * βk * codewordMeanPhotons C k))) :
    ENNReal.ofReal ((n : ℝ) * g ((1 - eta) * βk * codewordMeanPhotons C k)) ≤
      spectralEntropyNats (charlieCodeword eta C k) := by sorry

end GuhaBroadcast
