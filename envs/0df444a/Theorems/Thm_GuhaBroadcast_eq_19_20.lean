-- Prove2me | Theorems.Thm_GuhaBroadcast_eq_19_20
-- name    : GuhaBroadcast.eq_19_20
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:26:12.905292+00:00
-- url     : https://prove2.me/theorems/0e50e605-5be8-42a2-9200-1e73ded2bbe7
-- title:
--   Eqs. (19)–(20): average entropy at Bob and the bound on Bob's average Holevo information
-- statement:
--   Throughout, $\tfrac12<\eta\le 1$ is the beam-splitter transmissivity to Bob (the proof's standing assumption), $\bar N\ge 0$ is the photon budget, $n\ge 1$ is the block length, and $\mathcal C$ is a code with Bob's message set of size $M_B$, Charlie's of size $M_C$, encoder states $x^n(m,k)$ on $n$ modes, a POVM $\{\Lambda_{mk}\}$ for Bob and a POVM $\{\Lambda'_k\}$ for Charlie. The codebook-averaged total photon number of the codewords is at most $n\bar N$ (the paper's per-use budget $\langle\hat a^\dagger\hat a\rangle\le\bar N$, "averaged over the entire codebook", p.3). Messages are uniform: $p_{W_B}(m)=1/M_B$, $p_{W_C}(k)=1/M_C$. Bob's and Charlie's received states are $\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_{m,k}$; $\hat\rho^{B^n}_k=\sum_m p_{W_B}(m)\hat\rho^{B^n}_{m,k}$ and $\hat\rho^{C^n}_k=\sum_m p_{W_B}(m)\hat\rho^{C^n}_{m,k}$. Entropies $S$ are von Neumann entropies in nats, $\chi$ is the Holevo information (3), and $g(x)=(1+x)\log(1+x)-x\log x$.
--
--   Let $\hat\rho^{B^n}=\sum_k p_{W_C}(k)\hat\rho^{B^n}_k$. Then
--
--   1. $\sum_k p_{W_C}(k)S(\hat\rho^{B^n}_k)\le S(\hat\rho^{B^n})\le n\,g(\eta\bar N)$ (19);
--   2. there is $\beta\in[0,1]$ with $\sum_k p_{W_C}(k)S(\hat\rho^{B^n}_k)=n\,g(\eta\beta\bar N)$ and
--   $$
--   \sum_k p_{W_C}(k)\,\chi\big(p_{W_B}(m),\hat\rho^{B^n}_{m,k}\big)\le n\,g(\eta\beta\bar N)\quad(20).
--   $$
--
--   The number $\beta$ is the power split of the capacity region (8)–(9).
--
--   Differences from the source:
--   - generalization: a code of the achieving sequence of an achievable rate pair (p.3, 'any ... code in the achieving sequence') → every code satisfying the energy budget (and, where used, error ε), at a fixed block length n; reason: the inequality is a property of each code; the achieving-sequence codes are among them
--   - reading: 'the mean photon-number of the n-use average codeword at Bob ... is ηN̄' (p.4) → at most ηN̄ (resp. (1−η)N̄ at Charlie), the budget being codeEnergy ≤ nN̄; reason: the constraint ⟨â†â⟩ ≤ N̄ (p.2) is a budget; the bounds keep their direction because g is increasing
--   - reading: 'the convexity of von Neumann entropy' (after (19)) → Σ_k p_k S(ρ̂_k) ≤ S(Σ_k p_k ρ̂_k) (concavity); reason: the displayed inequality is the page's; only the word is misnamed
--   - encoding: entropy logarithm base unspecified → natural logarithm (nats), entropies in ℝ≥0∞; reason: a change of base scales every term
-- source:
--   Guha & Shapiro, Classical Information Capacity of the Bosonic Broadcast Channel, arXiv:0704.1901v2, Section III, eqs. (19)-(20), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P32
import Definitions.Def_GuhaBroadcast_mixture
import Definitions.Def_GuhaBroadcast_holevo
import Definitions.Def_GuhaBroadcast_bobOutput
import Definitions.Def_GuhaBroadcast_bobCodeword

open QAlgorithms.Papers.Independent.Next46.P32
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P39 (g)
open scoped ENNReal

namespace GuhaBroadcast

/-- Guha & Shapiro, *Classical Information Capacity of the Bosonic Broadcast Channel*, arXiv:0704.1901v2, Section III, Eqs. (19)–(20), p.4 (PDF page; the paper prints no page numbers): "the mean
photon-number of the n-use average codeword at Bob, ρ̂^{Bⁿ} ≡ Σ_k p_{W_C}(k)ρ̂_k^{Bⁿ}, is ηN̄. Hence,
0 ≤ Σ_k p_{W_C}(k)S(ρ̂_k^{Bⁿ}) ≤ S(ρ̂^{Bⁿ}) ≤ ng(ηN̄), (19) ... The monotonicity of g(x) then implies that
there is a β ∈ [0, 1], such that Σ_k p_{W_C}(k)S(ρ̂_k^{Bⁿ}) = ng(ηβN̄). Hence we have,
Σ_k p_{W_C}(k)χ(p_{W_B}(m), ρ̂_{m,k}^{Bⁿ}) ≤ ng(ηβN̄). (20)"

The per-code setup (shared by (14)–(25)): `1/2 < η ≤ 1` (the proof's standing assumption, p.2,
"if η > 1/2"), a budget `N̄ ≥ 0`, block length `n > 0`, and a code `C` with Bob decoding the pair `(m, k)`
and Charlie decoding `k` (p.1), whose codebook-averaged block energy is at most `n N̄` (p.3, "N̄ is the
average number of photons per-use at the transmitter (Alice) averaged over the entire codebook";
reading R4: the constraint `⟨â†â⟩ ≤ N̄` is a budget, not an exact mean).

**Formalization Note.** Uniform priors `p_{W_C}(k) = 1/M_C`, `p_{W_B}(m) = 1/M_B` (p.1, p.4). Reading R4:
the mean at Bob is **at most** `ηN̄` (the budget may not be spent), and (19) keeps its direction because
`g` is increasing. Reading R7: the step called "convexity of von Neumann entropy" is concavity; the
displayed inequality is the page's. (19) is stated in `ℝ≥0∞` (so `S(ρ̂^{Bⁿ})` is finite); the `β` clause
keeps both the equality, which (21) uses, and (20). No decoding property is used. -/
theorem eq_19_20 (eta Nbar : ℝ) (heta : 1 / 2 < eta) (heta1 : eta ≤ 1) (hNbar : 0 ≤ Nbar)
    {n MB MC : ℕ} (hn : 0 < n) (C : BroadcastCode n MB MC (Fin MB × Fin MC))
    (hE : codeEnergy C ≤ ENNReal.ofReal ((n : ℝ) * Nbar)) :
    (∑ k, spectralEntropyNats (bobCodeword eta C k)) / (MC : ℝ≥0∞) ≤
        spectralEntropyNats (mixture (fun _ : Fin MC => ((MC : ℝ)⁻¹)) (bobCodeword eta C)) ∧
      spectralEntropyNats (mixture (fun _ : Fin MC => ((MC : ℝ)⁻¹)) (bobCodeword eta C)) ≤
        ENNReal.ofReal ((n : ℝ) * g (eta * Nbar)) ∧
      ∃ β : ℝ, 0 ≤ β ∧ β ≤ 1 ∧
        (∑ k, (spectralEntropyNats (bobCodeword eta C k)).toReal) / (MC : ℝ) =
          (n : ℝ) * g (eta * β * Nbar) ∧
        (∑ k, holevo (fun _ : Fin MB => ((MB : ℝ)⁻¹)) (fun m => bobOutput eta C m k)) / (MC : ℝ) ≤
          (n : ℝ) * g (eta * β * Nbar) := by sorry

end GuhaBroadcast
