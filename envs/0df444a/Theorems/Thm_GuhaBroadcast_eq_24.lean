-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_24
-- name    : GuhaBroadcast.eq_24
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:38.359977+00:00
-- url     : https://prove2.me/theorems/19e83276-ca5b-4ede-ad15-6f85b501d4a9
-- title:
--   Eq. (24): bound on Charlie's Holevo information
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Then $S(\hat\rho^{C^n}_k)$ for every $k$ and $S\big(\sum_kp_{W_C}(k)\hat\rho^{C^n}_k\big)$ are finite, and
--
--   $$
--   \chi\big(p_{W_C}(k),\hat\rho^{C^n}_k\big)=S\Big(\sum_kp_{W_C}(k)\hat\rho^{C^n}_k\Big)-\sum_kp_{W_C}(k)S(\hat\rho^{C^n}_k)\le n\,g\big((1-\eta)\bar N\big)-\sum_kp_{W_C}(k)S(\hat\rho^{C^n}_k).
--   $$
--
--   The averaged state at Charlie has mean photon number at most $(1-\eta)\bar N$ per use, which bounds its entropy.
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - reading: 'the mean photon-number of the n-use average codeword at Bob ... is ηN̄' (p.4) → at most ηN̄ (resp. (1−η)N̄ at Charlie), the budget being codeEnergy ≤ nN̄; reason: the constraint ⟨â†â⟩ ≤ N̄ (p.2) is a budget; the bounds keep their direction because g is increasing
--   - encoding: entropies in χ treated as real numbers → entropies in ℝ≥0∞, χ formed with toReal, and the finiteness of every entropy entering χ asserted in the conclusion; reason: toReal reads +∞ as 0; asserting finiteness makes holevo exactly the paper's χ
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eq. (24), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_holevo
import Definitions.Def_GuhaBroadcast_charlieOutput
import Definitions.Def_GuhaBroadcast_charlieCodeword

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eq. (24), p.4 (PDF page; the paper prints no page numbers): "writing Charlie's
Holevo information as χ(p_{W_C}(k), ρ̂_k^{Cⁿ}) = S(Σ_k p_{W_C}(k)ρ̂_k^{Cⁿ}) − Σ_k p_{W_C}(k)S(ρ̂_k^{Cⁿ})
≤ ng((1 − η)N̄) − Σ_k p_{W_C}(k)S(ρ̂_k^{Cⁿ})".

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).

**Formalization Note.** Uniform prior `p_{W_C}(k) = 1/M_C`. The equality in (24) is the definition (3)
of `χ`. Reading R4: Charlie's mean photon number is at most `(1 − η)N̄`. The conclusion states that the
entropies entering `χ` are finite, so `holevo` is the paper's `χ`. At `η = 1` Charlie receives vacuum and
both sides are `0`. No decoding property is used. -/
theorem eq_24 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar)) :
    (spectralEntropyNats (mixture (fun _ : Fin MC => ((MC : ℝ)⁻¹)) (charlieCodeword eta C)) ≠ ⊤ ∧
      ∀ k, spectralEntropyNats (charlieCodeword eta C k) ≠ ⊤) ∧
    holevo (fun _ : Fin MC => ((MC : ℝ)⁻¹)) (charlieCodeword eta C) ≤
      (n : ℝ) * g ((1 - eta) * Nbar) -
        (∑ k, (spectralEntropyNats (charlieCodeword eta C k)).toReal) / (MC : ℝ) := by sorry

end GuhaBroadcast
