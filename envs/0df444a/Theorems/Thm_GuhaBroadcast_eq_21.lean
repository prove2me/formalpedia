-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_21
-- name    : GuhaBroadcast.eq_21
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:12.699369+00:00
-- url     : https://prove2.me/theorems/334db5bf-ca3f-43aa-b48c-385d0bdcffc7
-- title:
--   Eq. (21): $\frac1{M_C}\sum_k g(\eta\beta_k\bar N_k)=g(\eta\beta\bar N)$
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Let $\beta_k\in[0,1]$ satisfy $S(\hat\rho^{B^n}_k)=n\,g(\eta\beta_k\bar N_k)$ for every $k$ (17), and let $\beta\in[0,1]$ satisfy $\frac1{M_C}\sum_kS(\hat\rho^{B^n}_k)=n\,g(\eta\beta\bar N)$ (20). Then
--
--   $$
--   \sum_k\frac1{M_C}\,g(\eta\beta_k\bar N_k)=g(\eta\beta\bar N).
--   $$
--
--   This is the hypothesis of the entropy-mean inequality (22).
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - reading: N̄_{k_j} = 'the mean photon number of the jth symbol ρ̂_k^{B_j}' (p.3) → the input mean photon number of mode j of the k-th codeword, averaged over m (Bob's mode then has mean ηN̄_{k_j}); reason: (16) evaluates g(ηN̄_{k_j}), which bounds Bob's mode only when N̄_{k_j} is measured at the input
--   - encoding: 2^{nR_C} → M_C, the cardinality of Charlie's message set; reason: 2^{nR_C} is that cardinality
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (21), p.4

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

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (21), p.4 (PDF page; the paper prints no page numbers): "Equation (17), and
the uniform distribution p_{W_C}(k) = 1/2^{nR_C} imply that Σ_k (1/2^{nR_C}) g(ηβ_kN̄_k) = g(ηβN̄)."

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).
The `β_k` are those of (17) and `β` is that of (20).

**Formalization Note.** `2^{nR_C}` is the cardinality `M_C` of Charlie's message set. -/
theorem eq_21 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar))
    (βk : Fin MC → ℝ)
    (hβk : ∀ k, 0 ≤ βk k ∧ βk k ≤ 1 ∧ spectralEntropyNats (bobCodeword eta C k) =
      ENNReal.ofReal ((n : ℝ) * g (eta * βk k * codewordMeanPhotons C k)))
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hβ : (∑ k, (spectralEntropyNats (bobCodeword eta C k)).toReal) / (MC : ℝ) =
      (n : ℝ) * g (eta * β * Nbar)) :
    (∑ k, g (eta * βk k * codewordMeanPhotons C k)) / (MC : ℝ) = g (eta * β * Nbar) := by sorry

end GuhaBroadcast
