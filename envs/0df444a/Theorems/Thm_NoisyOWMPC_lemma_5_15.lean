-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_15
-- name    : NoisyOWMPC.lemma_5_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:06:47.882193+00:00
-- url     : https://prove2.me/theorems/1ff79729-d60d-46cd-88f2-4cd833e6da7b
-- title:
--   Lemma 5.15 — recoverability of the release test
-- statement:
--   Let receiver $i$ have a bit $\beta_i$ satisfying noise preservation, take an expander family as in Corollary A.8 with $(c,\gamma)=(8,2/5)$ and rational approximations $\mathrm{apx}$. There is a constant $K$ such that for every polynomial $M\ge\lambda^5$ with $M+1$ a power of two and all large $\lambda$, in the seeded experiment of Construction 5.11
--   $$\Pr_{\mathrm{st},\sigma}\bigl[H(\mathrm{st})=0\text{ and }\exists w:Q_{\mathrm{Recons}(\mathrm{st},\sigma)}(w)=1\text{ and }\sigma\notin\mathrm{Rec}(\mathrm{st},w)\bigr]\le\delta_{\mathrm{rel}}=KM^{-1/10}.$$
--
--   After an honest rejection, every accepting query identifies the seed. The proof of this lemma in Appendix B.2 is AI-assisted (p.42).
--
--   Differences from the source:
--   - reading: δ_rel = O(M^{−1/10}) → K M^{−1/10} with K independent of M, for all sufficiently large λ; reason: standard reading of O
--   - generalization: the expander of Corollary A.8 with the paper's parameters (GUV graph, labels F_{M+1}^r) → any expander family satisfying the conclusion of Corollary A.8 for the stated (c, γ) (IsA8Family); reason: the statement then holds for the paper's GUV-based graph, which is one such family (Corollary A.8)
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.15, p.28 (setting of Lemma 5.10, p.26; proof §B.2.4, p.53)

import Mathlib
import Definitions.Def_NoisyOWMPC_releaseTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC

/-- **Lemma 5.15 (Recoverability of the release test)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.15, p.28, in the setting of Lemma 5.10, p.26): "In the
seeded experiment of Construction 5.11,
`Pr_{st,σ}[H(st) = 0 and ∃ w : Q_{Recons(st,σ)}(w) = 1 and σ ∉ Rec(st, w)] ≤ δ_rel`,
`δ_rel = O(M^{−1/10})`."

Setting: receiver `i` with a bit `β_i` satisfying noise preservation (Definition 4.5), Construction
5.11 with the release expander of a family as in Corollary A.8 with `(c, γ) = (8, 2/5)` (p.26),
rational approximations `apx`, and every polynomial `M ≥ λ⁵` with `M + 1` a power of two.

**Formalization Note** `O(M^{−1/10})` is `K M^{−1/10}` for a constant `K` (depending on the channel,
`β`, the expander family and `apx`, not on `M`) and all large `λ`. -/
theorem lemma_5_15 {k : ℕ} {X : Type} [Fintype X] {Y : Fin k → Type} [∀ i, Fintype (Y i)]
    (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool) (i : Fin k)
    (hβ : NoisePreservingAt C i (β i))
    (Gr : (M ℓ G : ℕ) → LayeredGraph M) (hGr : IsA8Family Gr 8 (2 / 5))
    (apx : ℕ → ∀ i, X → Y i → ℚ) (hapx : IsApx C apx) :
    ∃ K : ℝ, ∀ M : ℕ → ℕ, AdmissibleM M → ∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
      wprob ((releaseTest C apx β M i Gr).seedW lam) (fun z =>
          (releaseTest C apx β M i Gr).H lam z.1 = false ∧ ∃ w,
            (releaseTest C apx β M i Gr).test lam
              ((releaseTest C apx β M i Gr).recons lam z.1 z.2) w = true ∧
            z.2 ∉ (releaseTest C apx β M i Gr).recov lam z.1 w) ≤
        K * (M lam : ℝ) ^ (-(1 / 10 : ℝ)) := by sorry

end NoisyOWMPC
