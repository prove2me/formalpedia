-- Prove2me | Theorems.Thm_NashAmplification_Filtering_theorem_1_1
-- name    : NashAmplification.Filtering.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:23:19.709442+00:00
-- url     : https://prove2.me/theorems/1a8e24c9-7bbe-4955-92da-cd73f6243763
-- title:
--   Theorem 1.1 — polynomial-time construction and recovery
-- statement:
--   Fix an integer $k\ge2$, real parameters $\delta,\varepsilon\in(0,1)$ and $\eta\in[0,1)$. There exist $C\ge2$ and two deterministic algorithms, chosen independently of the action-set sizes. For every rational complete-table $k$-player game $G$ with payoffs in $[0,1]$ and nonempty action sets, construction returns a complete-table symmetric binary-payoff $C$-player game $H$ in polynomial time in the actual input length $M$. From every supplied rational $(\varepsilon,\eta)$-weak approximate Nash equilibrium $\sigma$ of $H$, recovery returns a rational $\delta$-approximate Nash equilibrium of $G$ in polynomial time in $M+L_\sigma$:
--   $$G\longmapsto H,\qquad(G,\sigma)\longmapsto x,\qquad\sigma\in\operatorname{WeakANE}_{\varepsilon,\eta}(H)\Longrightarrow x\in\operatorname{ANE}_\delta(G).$$
--   The two machine witnesses and their polynomial time bounds precede every input game. Thus their polynomial degrees and $C$ depend only on $k,\delta,\varepsilon,\eta$. The supplied numerator/denominator pairs may be unreduced, and $L_\sigma$ is their actual length, without any assumed bound in terms of $M$. No complexity conjecture is a hypothesis.
--
--   This is the unconditional reduction underlying the paper's hardness amplification.
--
--   Differences from the source:
--   - encoding: finite nonempty action sets and one-based player indices → positive action counts with Fin indices, mixed-radix table order, and zero-based coordinates; reason: finite relabeling preserves every source game and distribution
--   - encoding: pure unilateral deviations and a maximum gain bound → all mixed unilateral deviations in IsEpsApproxNash; reason: the proved mixed_deviation and ane_iff equivalences recover exactly (2.1)
--   - encoding: at most floor(ηC) violating players → at least (1-η)C players satisfy the mixed best-response condition; reason: best_response_iff and weak_iff prove equivalence, including the integer floor
--   - encoding: explicit rational tables and profile lists with binary numerators and denominators, time M+Lσ → raw unreduced pairs, explicit size headers and delimiters, with a tagged concatenation of G and σ as recovery input; reason: the proved exact length formulas give only constant per-entry overhead and preserve the actual supplied probabilities; the encoder never evaluates construct
--   - encoding: deterministic polynomial bit-operation time → Nonempty TM2ComputableInPolyTime for each of the two fixed encoders; reason: FinTM2 steps and bit operations are polynomially related, and the machines and polynomials are existential conclusions
--   - generalization: the recovery calculation accepts a supplied profile of H and may report failure outside its promise → a total recovery function on all shaped rational profile lists, including wrong dimensions or nonnormalized lists, with correctness under the source premise; reason: the algorithm can check input shape and normalization in polynomial time and use a fixed rational default outside its promised domain
-- source:
--   Deng, Li, Wang and Zhang, Hardness Amplification for Approximate Nash Equilibrium with a Constant Number of Players, STOC 2027 submission #120 (October 2026), SHA-256 c201a27da9b9920a924945f1a30c7919ae6b922c99430223ee9bbcdec5b0ffa8, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/120.pdf, Theorem 1.1, PDF p. 3 (printed p. 2)

import Definitions.Def_NashAmplification_Filtering_Encoding

open scoped BigOperators
noncomputable section

namespace NashAmplification.Filtering

/-- Theorem 1.1, PDF 3. Both fixed machines precede every game size and input.
The recovery input encoder reads G and σ directly, never construct G. -/
theorem theorem_1_1 (k : ℕ) (hk : 2 ≤ k) (δ ε η : ℝ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) (hε : ε ∈ Set.Ioo (0 : ℝ) 1)
    (hη : η ∈ Set.Ico (0 : ℝ) 1) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∃ construct : Table k → Table C,
    ∃ recover : Table k × RawProfile C → RawProfile k,
      Nonempty (Turing.TM2ComputableInPolyTime encGame encGame construct) ∧
      Nonempty (Turing.TM2ComputableInPolyTime encGameProfile encProfile recover) ∧
      ∀ G : Table k, ∃ n : ℕ, 0 < n ∧
        (construct G).sizes = List.replicate C n ∧
        IsSymmetric (uniformUtility (construct G) n) ∧
        IsBinary (uniformUtility (construct G) n) ∧
        ∀ σ : RawProfile C, σ.sizes = List.replicate C n →
          RubinsteinNash.WeakNash.IsWeakNash (uniformUtility (construct G) n)
            (uniformProfile σ n) ε η →
          (recover (G,σ)).sizes = G.sizes ∧
          DGPNash.WellSupported.IsEpsApproxNash G.utility
            ((recover (G,σ)).on G.counts) δ := by sorry
end NashAmplification.Filtering
