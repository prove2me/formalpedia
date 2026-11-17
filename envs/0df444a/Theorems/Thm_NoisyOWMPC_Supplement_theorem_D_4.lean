-- Prove2me | Theorems.Thm_NoisyOWMPC_Supplement_theorem_D_4
-- name    : NoisyOWMPC.Supplement.theorem_D_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:07:33.505662+00:00
-- url     : https://prove2.me/theorems/d307f217-6204-4aae-96ed-ee4083c0d3d3
-- title:
--   Theorem D.4 — random string OT from string erasures (corrected: subset-selector part for N at least a constant N₀)
-- statement:
--   Assume an indistinguishability obfuscator and one-way functions, and let $n(\lambda)$ be the input length of the injective one-way function they give.
--
--   1. For all polynomial lengths $\ell$, $L \ge n(\lambda)$ and $N$, every recoverable selector on $[N]$ with errors $(\alpha_{\mathrm{sel}}, \delta_{\mathrm{sel}})$ and seed length $\kappa_{\mathrm{sel}} \ge n(\lambda)$, and every polynomial-time generator of the Fig. 11 program, Construction D.3 (padded to any large enough polynomial size) realizes $\mathrm{ROT}^\ell$ over $N$ uses of the ideal string erasure channel $\mathrm{SEC}^{N,L}_{1/2}$ and one noiseless message, with
--   $$
--   \varepsilon_{\mathrm{cor}} \le \alpha_{\mathrm{sel}}, \qquad \varepsilon_{\{1\}} \le \delta_{\mathrm{sel}} + \mathrm{negl}(\lambda), \qquad \varepsilon_S \le \alpha_{\mathrm{sel}} \ \text{(statistically)},
--   $$
--   and the protocol is Las Vegas and efficient.
--   2. With the subset selector of Construction 5.17, $\alpha_{\mathrm{sel}} = b_N = 2e^{-2r_N^2/N}$ is negligible; there is a constant $K$ such that for every admissible polynomial $N \ge N_0$ (with seed length at least $n(\lambda)$) the receiver error satisfies $\delta_{\mathrm{sel}} \le K N^{-0.013}$ for large $\lambda$; and for every $c > 0$ a polynomial $N$ makes all three errors at most $\lambda^{-c}$ for large $\lambda$.
--
--   Random string OT over a string erasure channel follows the complementary-release strategy of prior work with an indistinguishability obfuscator in place of ideal obfuscation; the channel alphabet $\{0,1\}^L$ grows with $\lambda$.
--
--   **Formalization Note** The receiver's $\mathrm{negl}(\lambda)$ is the negligible term of $\approx^c$. The statistical sender error is measured against the paper's simulator, a fresh run of the sender. $O(\cdot)$ is a constant independent of $N$.
--
--   Differences from the source:
--   - generalization: 'assume iO and one-way functions', with the injective OWF F of §5 whose input length n(λ) bounds L and κ_sel → every iO scheme O and every injective one-way function Finj with Finj.n ≤ L and Finj.n ≤ κ_sel; reason: Theorem 3.4 gives such an F from iO and one-way functions; the paper's F is one of them (as in the base Theorem 5.25)
--   - generalization: the paper's program padded to 'the common size' → every polynomial-time Fig. 11 generator and every polynomial pad size above some s₀; reason: the paper's implementation is one such generator and size (as in the base Theorem 5.25)
--   - encoding: N uses of an ideal string erasure channel; the receiver obtains (V, x|_V) → SECProtocol with a λ-indexed alphabet {0,1}^{L(λ)} ∪ {⊥}; the observation is the partial word x|_V; reason: Remark D.7: the alphabet grows with λ; V is determined by x|_V
--   - reading: sender security error ε_S ≤ α_sel, statistically → statistical distance ≤ α_sel between (x, y, view_S) and (x, ȳ, view′_S) with view′_S a fresh run of the sender (its exact reference law); reason: the paper's simulator 'runs the sender … and outputs its random coins, the strings x, and the program' (p.60); exact reference distributions (p.24)
--   - encoding: δ_sel = O(N^{−0.013}); 'every prescribed inverse-polynomial error' → ∃ K with δ_sel ≤ K N^{−0.013} for large λ; ∀ c > 0 ∃ admissible N with errors ≤ λ^{−c} for large λ; reason: standard reading of O(·) (base decision 8); every inverse polynomial is eventually above some λ^{−c}
--   - correction: with the subset selector of Construction 5.17 (every even polynomial N ≥ λ) → every admissible N with N(λ) ≥ N₀ for a constant N₀; reason: false for small N: N(λ) = 2λ + 2 at λ = 1 gives N = 4, q₀ = 1, m = 0, so b_S ≡ 0 and the guard accepts every set (r_4 = 2); the sender's view fixes b = π and the statistical sender error is 1/2 > b_4 = 2e^{−2}
--   - generalization: the expander of Corollary A.8 used by Construction 5.17 → any expander family satisfying the conclusion of Corollary A.8 for (c, γ) = (2, 2/5) (IsA8Family); reason: the paper's graph is one such family (as in the base Lemma 5.16)
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem D.4, pp.58–59 (proof, p.60; Remark D.7, p.60)

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_constructionD3
import Definitions.Def_NoisyOWMPC_Selector
import Definitions.Def_NoisyOWMPC_selectorTest
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_IsA8Family
import Definitions.Def_NoisyOWMPC_KeyedFamily

namespace NoisyOWMPC.Supplement

/-- **Theorem D.4 (Random string OT from string erasures)** (Ishai, Lu, Zafar, *Non-Interactive
Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem D.4, pp.58–59): "Assume iO and one-way functions.
Construction D.3 realizes `ROT^ℓ` in the sense of Definition 4.2, using `N` uses of an ideal string
erasure channel with erasure probability `1/2` and one noiseless message, with correctness error
`α_sel`, receiver security error `ε_{1} ≤ δ_sel + negl(λ)`, and sender security error
`ε_S ≤ α_sel`, statistically. The protocol is Las Vegas. With the subset selector of
Construction 5.17, `α_sel` is negligible and `δ_sel = O(N^{−0.013})`, so every prescribed
inverse-polynomial error is attained with a polynomial `N`."

For an iO scheme `O` and an injective one-way function `Finj` with input length `n(λ)`:
1. for all public polynomial lengths `ℓ`, `L_s ≥ n(λ)`, `N`, every recoverable selector on `[N]`
   with errors `(α_sel, δ_sel)` and seed length `κ_sel ≥ n(λ)`, and every polynomial-time Fig. 11
   generator, every large enough polynomial pad size makes Construction D.3 a protocol with
   correctness error `α_sel`, receiver security error `δ_sel` (`≈^c`, whose negligible term is the
   `negl(λ)`), statistical sender security error `α_sel`, Las Vegas, exactly `N` channel uses of
   string length `L_s`, one noiseless message of the fixed transmission length, and efficient;
2. for the subset selector of Construction 5.17 (with a small hit-threshold constant `γ_sel` and
   expanders as in Corollary A.8): `α_sel = b_N` is negligible for every admissible `N`; there are
   `K` and `N₀` such that for every admissible `N ≥ N₀` with seed length `≥ n(λ)` the protocol has
   correctness and statistical sender errors `b_N` and receiver error `δ_sel ≤ K N^{−0.013}` for
   large `λ`; and for every `c > 0` some admissible `N` makes all three errors at most `λ^{−c}`
   for large `λ`.

**Formalization Note** "Assume iO and one-way functions" is an iO scheme and the injective one-way
function they give (Theorem 3.4), whose input length `n(λ)` bounds the seed and string lengths
(Construction D.3, p.58). The channel alphabet grows with `λ` (Remark D.7), hence `SECProtocol`.
`O(·)` is a constant `K` independent of `N`, with the bound for large `λ`. Correction (inherited
from Lemma 5.16): part 2 asks `N(λ) ≥ N₀` for a constant `N₀`; for `N(λ) = 2λ + 2` at `λ = 1`,
`N = 4` gives `q₀ = 1`, `m = 0`, the coin `b_S ≡ 0` and a guard accepting every set, so the sender's
view fixes `b = π` and the statistical sender error is `1/2 > b_4 = 2e^{−2}`. -/
theorem theorem_D_4 (O : IOScheme) (hO : O.IsIO) (Finj : KeyedFamily) (hFinj : Finj.IsInjOWF) :
    -- (1) Construction D.3 with any recoverable selector
    (∀ (ℓ Ls N : ℕ → ℕ), PolyParam ℓ → PolyParam Ls → PolyParam N →
      (∀ lam, Finj.n lam ≤ Ls lam) →
      ∀ (S : Selector N) (αsel δsel : ℕ → ℝ), S.IsRecSelector αsel δsel →
        (∀ lam, Finj.n lam ≤ S.κ lam) →
        ∀ gen : ProgGen11 ℓ Ls N S.toSelHalf, IsFig11Gen ℓ Ls N S.toSelHalf gen →
          ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
            (constructionD3 ℓ Ls N S.toSelHalf O gen s).CorrErr αsel ∧
            (constructionD3 ℓ Ls N S.toSelHalf O gen s).SecErrRecv δsel ∧
            (constructionD3 ℓ Ls N S.toSelHalf O gen s).SecErrStatS αsel ∧
            (constructionD3 ℓ Ls N S.toSelHalf O gen s).LasVegas ∧
            (∀ lam, (constructionD3 ℓ Ls N S.toSelHalf O gen s).N lam = N lam) ∧
            (∀ lam, (constructionD3 ℓ Ls N S.toSelHalf O gen s).Ls lam = Ls lam) ∧
            (∀ lam, (constructionD3 ℓ Ls N S.toSelHalf O gen s).L lam =
              txLenG O (inLen11 Ls N) (size11 ℓ s) lam) ∧
            (constructionD3 ℓ Ls N S.toSelHalf O gen s).IsEfficient) ∧
    -- (2) the subset selector of Construction 5.17
    (∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ γsel : ℚ, 0 < γsel → (γsel : ℝ) < γ₀ →
      ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 2 (2 / 5) →
        (∀ N : ℕ → ℕ, AdmissibleN N → Negligible fun lam => bN (N lam)) ∧
        (∃ (K : ℝ) (N₀ : ℕ), ∀ (ℓ Ls N : ℕ → ℕ), PolyParam ℓ → PolyParam Ls → AdmissibleN N →
          (∀ lam, N₀ ≤ N lam) → (∀ lam, Finj.n lam ≤ Ls lam) →
          (∀ lam, Finj.n lam ≤ (selectorTest N Gr γsel).κ lam) →
          ∀ gen : ProgGen11 ℓ Ls N (selectorHalf N), IsFig11Gen ℓ Ls N (selectorHalf N) gen →
            ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
              (constructionD3 ℓ Ls N (selectorHalf N) O gen s).CorrErr (fun lam => bN (N lam)) ∧
              (constructionD3 ℓ Ls N (selectorHalf N) O gen s).SecErrStatS (fun lam => bN (N lam)) ∧
              ∃ δsel : ℕ → ℝ, (∃ lam₀ : ℕ, ∀ lam ≥ lam₀,
                  δsel lam ≤ K * (N lam : ℝ) ^ (-(13 / 1000 : ℝ))) ∧
                (constructionD3 ℓ Ls N (selectorHalf N) O gen s).SecErrRecv δsel) ∧
        ∀ c : ℝ, 0 < c → ∀ (ℓ Ls : ℕ → ℕ), PolyParam ℓ → PolyParam Ls →
          (∀ lam, Finj.n lam ≤ Ls lam) →
          ∃ N : ℕ → ℕ, AdmissibleN N ∧ (∀ lam, Finj.n lam ≤ (selectorTest N Gr γsel).κ lam) ∧
            ∀ gen : ProgGen11 ℓ Ls N (selectorHalf N), IsFig11Gen ℓ Ls N (selectorHalf N) gen →
              ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
                ∃ ε : ℕ → ℝ, (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ε lam ≤ (lam : ℝ) ^ (-c)) ∧
                  (constructionD3 ℓ Ls N (selectorHalf N) O gen s).CorrErr ε ∧
                  (constructionD3 ℓ Ls N (selectorHalf N) O gen s).SecErrRecv ε ∧
                  (constructionD3 ℓ Ls N (selectorHalf N) O gen s).SecErrStatS ε) := by sorry

end NoisyOWMPC.Supplement
