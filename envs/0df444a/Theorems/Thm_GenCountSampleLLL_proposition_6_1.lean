-- Prove2me | Theorems.Thm_GenCountSampleLLL_proposition_6_1
-- name    : GenCountSampleLLL.proposition_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:56.791507+00:00
-- url     : https://prove2.me/theorems/1ad5f834-8cb9-4548-bfc2-e8a80d15e5bb
-- title:
--   Proposition 6.1, p.20 — $\|\mu^-K^N-\mu^+\|_{\mathrm{TV}}<\delta/10$ for $\beta=\delta/(100(1+2m))$, $N=\lceil200{,}000(m+1)^2\delta^{-3}\rceil$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$, let $m=|\mathcal C|$ and $a\in\mathcal D\subseteq\mathcal C$. For $0<\delta\le1$ let
--   $$
--   \beta=\frac{\delta}{100(1+2m)},\qquad N=\big\lceil200{,}000(m+1)^2\delta^{-3}\big\rceil,
--   $$
--   and $K=K^\beta_{\mathcal D,a}$. Then
--   $$
--   \big\|\mu^-K^N-\mu^+\big\|_{\mathrm{TV}}<\frac\delta{10}.
--   $$
--
--   Running $K$ for $N$ steps from an input state is the insertion map of Proposition 2.2.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: µ⁻K^N, ‖·‖_TV, δ⁻³ → the row vector µ⁻ times the N-th matrix power of K; ½ Σ |·| (`IsingLTL.BeliefProp.tvDist`); 1/δ³; reason: the paper's TV normalization (p.29)
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Proposition 6.1, p.20

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_insertionChain
import Definitions.Def_IsingLTL_BeliefProp_TVDist

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Proposition 6.1, p.20 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with
`c = 1/100`. Fix `a ∈ D ⊆ C`. For `0 < δ ≤ 1`, let `β = δ/(100(1 + 2m))` and
`N = ⌈200,000 (m + 1)² δ⁻³⌉`. Then `‖µ⁻ K^N − µ⁺‖_TV < δ/10`, for `K = K^β_{D,a}`.

**Formalization Note.** `µ⁻K^N` is the row vector `µ⁻` times the `N`-th matrix power of `K`;
`‖·‖_TV` is `½ Σ |·|` on the finite state space (`IsingLTL.BeliefProp.tvDist`, the normalization
of p.29). `m = |C|`. -/
theorem proposition_6_1 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D)
    (δ : ℝ) (hδ : 0 < δ ∧ δ ≤ 1) :
    IsingLTL.BeliefProp.tvDist
        (Matrix.vecMul (I.muMinus D a)
          (I.Kker (δ / (100 * (1 + 2 * (I.m : ℝ)))) D a ^
            ⌈200000 * ((I.m : ℝ) + 1) ^ 2 / δ ^ 3⌉₊))
        (I.muPlus D a) < δ / 10 := by sorry

end GenCountSampleLLL
