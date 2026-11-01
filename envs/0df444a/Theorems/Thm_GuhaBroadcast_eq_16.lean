-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_16
-- name    : GuhaBroadcast.eq_16
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:58.859517+00:00
-- url     : https://prove2.me/theorems/9f315b85-eb77-442c-93d5-ea05bd2c1eb4
-- title:
--   Eq. (16): entropy bound on Bob's codeword states
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Let $\bar N_{k_j}$ be the input mean photon number of mode $j$ of codeword $k$ (averaged over Bob's message) and $\bar N_k=\frac1n\sum_j\bar N_{k_j}$. Then for every $k$
--
--   $$
--   0\le S\big(\hat\rho^{B^n}_k\big)\le\sum_{j=1}^n g(\eta\bar N_{k_j})\le n\,g(\eta\bar N_k).
--   $$
--
--   In particular every $S(\hat\rho^{B^n}_k)$ is finite. This turns the photon budget into an entropy budget for Bob.
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - reading: N̄_{k_j} = 'the mean photon number of the jth symbol ρ̂_k^{B_j}' (p.3) → the input mean photon number of mode j of the k-th codeword, averaged over m (Bob's mode then has mean ηN̄_{k_j}); reason: (16) evaluates g(ηN̄_{k_j}), which bounds Bob's mode only when N̄_{k_j} is measured at the input
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (16), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_bobCodeword
import Definitions.Def_GuhaBroadcast_modeMeanPhotons
import Definitions.Def_GuhaBroadcast_codewordMeanPhotons

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (16), p.3 (PDF page; the paper prints no page numbers):
"0 ≤ S(ρ̂_k^{Bⁿ}) ≤ Σ_{j=1}^n g(ηN̄_{k_j}) ≤ ng(ηN̄_k)", where "N̄_k ≡ Σ_{j=1}^n (1/n)N̄_{k_j}, and N̄_{k_j}
is the mean photon number of the jth symbol ... of the n-symbol codeword ρ̂_k^{Bⁿ}".

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).

**Formalization Note.** `0 ≤ S` is automatic in `ℝ≥0∞`. Reading R5: `N̄_{k_j}` is the input mean of
mode `j` averaged over `m` (`modeMeanPhotons`), so Bob's j-th mode has mean `η N̄_{k_j}`. The first
inequality, in `ℝ≥0∞`, also gives the finiteness of `S(ρ̂_k^{Bⁿ})`. No decoding property is used. -/
theorem eq_16 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar)) (k : Fin MC) :
    spectralEntropyNats (bobCodeword eta C k) ≤
        ENNReal.ofReal (∑ j, g (eta * modeMeanPhotons C k j)) ∧
      ∑ j, g (eta * modeMeanPhotons C k j) ≤ (n : ℝ) * g (eta * codewordMeanPhotons C k) := by sorry

end GuhaBroadcast
