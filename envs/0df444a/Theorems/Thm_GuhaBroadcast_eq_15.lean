-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_15
-- name    : GuhaBroadcast.eq_15
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:25:54.587988+00:00
-- url     : https://prove2.me/theorems/896105ff-b942-4a3e-b74c-6a373842e326
-- title:
--   Eq. (15): Fano, Holevo and convexity bound on Bob's rate
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   The code has error at most $\varepsilon\ge0$ in the sense of (2): $\operatorname{Tr}\big(\hat\rho_{x^n(m,k)}(\Lambda_{mk}\otimes\Lambda'_k)\big)\ge 1-\varepsilon$ for **every** pair $(m,k)$.
--
--   Let $\hat\rho^{B^n}_m=\sum_k p_{W_C}(k)\hat\rho^{B^n}_{m,k}$. Then all entropies $S(\hat\rho^{B^n}_{m,k})$, $S(\hat\rho^{B^n}_m)$, $S(\hat\rho^{B^n}_k)$, $S\big(\sum_m p_{W_B}(m)\hat\rho^{B^n}_m\big)$ are finite, and
--
--   1. $(1-\varepsilon)\log M_B\le\chi\big(p_{W_B}(m),\hat\rho^{B^n}_m\big)+\log 2$;
--   2. $\chi\big(p_{W_B}(m),\hat\rho^{B^n}_m\big)\le\sum_k p_{W_C}(k)\,\chi\big(p_{W_B}(m),\hat\rho^{B^n}_{m,k}\big)$.
--
--   Together these are (15): $nR_B\le\chi(p_{W_B}(m),\hat\rho^{B^n}_m)+n\epsilon''_n\le\sum_kp_{W_C}(k)\chi(p_{W_B}(m),\hat\rho^{B^n}_{m,k})+n\epsilon''_n$, with Fano's term made explicit.
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - reading: ε″_n → 0 left implicit in the Fano step → the explicit Fano term: (1 − ε) log M_B ≤ χ + log 2, i.e. nε″_n = log 2 + ε log M_B; reason: Fano's inequality for uniform messages with error ε; with ε_n → 0 this is the paper's ε_n → 0
--   - reading: 'the concavity of Holevo information' (last line of (15)) → χ(p_m, Σ_k p_k ρ̂_{m,k}) ≤ Σ_k p_k χ(p_m, ρ̂_{m,k}) (convexity in the states for fixed priors); reason: the displayed inequality is the page's; only the word is misnamed
--   - encoding: nR = H(W) with message sets of size 2^{nR}, logarithm base unspecified → log M with M the cardinality of Fin M, natural logarithm; reason: 2^{nR} is the set size; a change of base scales both sides
--   - encoding: entropies in χ treated as real numbers → entropies in ℝ≥0∞, χ formed with toReal, and the finiteness of every entropy entering χ asserted in the conclusion; reason: toReal reads +∞ as 0; asserting finiteness makes holevo exactly the paper's χ
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (15), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_holevo
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_bobCodeword
import Definitions.Def_GuhaBroadcast_bobMessageState

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (15), p.3 (PDF page; the paper prints no page numbers):
"nR_B = H(W_B) ≤ I(W_B; Ŵ_B) + nε″_n ≤ χ(p_{W_B}(m), ρ̂_m^{Bⁿ}) + nε″_n
≤ Σ_k p_{W_C}(k) χ(p_{W_B}(m), ρ̂_{m,k}^{Bⁿ}) + nε″_n", by Fano's inequality, Holevo's bound and "the
concavity of Holevo information".

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).
The code is a `(2^{nR_B}, 2^{nR_C}, n, ε)` code in the sense of (2), p.1: the joint success
probability `Tr ρ̂_{x^n(m,k)} (Λ_{mk} ⊗ Λ′_k)` is at least `1 − ε` for **every** `(m, k)`.

**Formalization Note.** `nR_B = log M_B` (uniform messages, nats). Reading R6: `nε″_n = log 2 + ε log M_B`
(Fano), giving `(1 − ε) log M_B ≤ χ(p_{W_B}(m), ρ̂_m^{Bⁿ}) + log 2`; Bob's decision on `m` comes from
marginalizing his POVM over `k`. Reading R7: the last step, called "concavity" on the page, is the
inequality `χ(p_m, Σ_k p_k ρ̂_{m,k}) ≤ Σ_k p_k χ(p_m, ρ̂_{m,k})` (convexity of `χ` in the states for
fixed priors); the displayed inequality is the page's. Both the middle and the last link are stated.
`ρ̂_m^{Bⁿ}` is `bobMessageState` and `ρ̂_k^{Bⁿ}` is `bobCodeword`. The conclusion also states that every
entropy entering a `χ` here is finite, so each `holevo` is exactly the paper's `χ`. -/
theorem eq_15 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar))
    (ε : ℝ) (hε : 0 ≤ ε)
    (hsucc : ∀ m k, 1 - ε ≤ broadcastSuccessProbability C (broadcast n eta) m k (m, k)) :
    (spectralEntropyNats (mixture (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (bobMessageState eta C)) ≠ ⊤ ∧
      (∀ m, spectralEntropyNats (bobMessageState eta C m) ≠ ⊤) ∧
      (∀ k, spectralEntropyNats (bobCodeword eta C k) ≠ ⊤) ∧
      (∀ m k, spectralEntropyNats (bobOutput eta C m k) ≠ ⊤)) ∧
    (1 - ε) * Real.log (MB : ℝ) ≤
      holevo (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (bobMessageState eta C) + Real.log 2 ∧
    holevo (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (bobMessageState eta C) ≤
      (∑ k, holevo (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (fun m => bobOutput eta C m k)) / (MC : ℝ) := by sorry

end GuhaBroadcast
