-- Prove2me | Theorems.Thm_MaxCompForest_theorem_F_1
-- name    : MaxCompForest.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:39:04.057062+00:00
-- url     : https://prove2.me/theorems/ce7c89cb-6d25-4f0a-88f9-fbf90f3b4a1a
-- title:
--   Theorem F.1 — greedy-pivot rational slow-response factor, with the bound (F.19)
-- statement:
--   There is one machine and an absolute exponent $b$ with the following property. Let $H$ be a connected loopless multigraph on $n$ vertices with positive rational conductances, $1\le q<n$, $0<\gamma\le1$ and $0<\theta\le1$ rational, and $\lambda_{q+1}(N)\ge\gamma$. On this input, of binary length $L$, the machine halts within $(\lceil\gamma^{-1}\rceil+L+2)^b$ steps and outputs a rational cutoff $c\in[\gamma/4,\gamma/2]$, an integer $r$ and a rational $r\times n$ matrix $\mathbf F$ such that:
--
--   1. $N$ has no eigenvalue in $[c-\tau,c+\tau]$, with $\tau=\gamma/(16q)$;
--   2. $r\le q-1$ is the number of positive eigenvalues of $N$ below $c$;
--   3. with $R=D^{-1/2}\big[\sum_{0<\lambda_a<c}(\lambda_a^{-1}-1)u_au_a^{\top}\big]D^{-1/2}$,
--   $$
--   \|\mathbf F^{\top}\mathbf F-R\|_{\mathrm{op}}\le\theta/d_{\max}.
--   $$
--
--   This produces rational features for the slow response without an eigenvector oracle, and the polynomial bound is what the final running time needs.
--
--   Differences from the source:
--   - reading: “a deterministic algorithm … bit time” → one Mathlib multi-stack machine `TM2ComputableAux Sym Sym` on a fixed binary encoding; reason: the paper names no machine; a bit-operation algorithm and a multi-stack machine differ by a polynomial, which the time bound absorbs with changed absolute constants
--   - generalization: bit complexity $f(q,\gamma^{-1})\,\mathrm{poly}(L,\log\theta^{-1})$ with an unspecified $f$ → the polynomial bound $(\lceil\gamma^{-1}\rceil+L+2)^b$; reason: the paper proves this bound on pp.45–46 and the goal needs it; it implies the printed bound and, since output length is at most a constant times the time, (F.19)–(F.20)
--   - reading: “a certified eigenvalue-free interval around it” → no eigenvalue in $[c-\gamma/(16q),c+\gamma/(16q)]$; reason: the interval of Lemma F.3, p.42, which is the certificate the proof gives
--   - encoding: the algorithm is run under the theorem's hypotheses → behaviour outside the hypotheses is unconstrained, including non-halting; reason: the theorem assumes the promise; the machine is not asked to verify it
-- source:
--   Chao–Ma–Gao–Cen–Wang, Maximum-Completion Forests via Sharp Spectral Quantization, STOC 2027 submission (manuscript sha256 48edea4274461ccd90489c3ddd2e07e5628e8f897e0b81d21055e99f6a7a83e2), Theorem F.1, p.42; pp.45–46; Lemma F.3, p.42

import Mathlib
import Definitions.Def_MaxCompForest_RInst
import Definitions.Def_MaxCompForest_lam
import Definitions.Def_MaxCompForest_deg
import Definitions.Def_MaxCompForest_slowResp
import Definitions.Def_MaxCompForest_slowCount
import Definitions.Def_MaxCompForest_dmax
import Definitions.Def_MaxCompForest_featGram
import Definitions.Def_MaxCompForest_ratFeat
import Definitions.Def_MaxCompForest_encFactorIn
import Definitions.Def_MaxCompForest_encFactorOut
import Definitions.Def_CFLOutliers_OutputsWithin
import Definitions.Def_OnlineCRS_Combine_Sym
open EffResSparsify.ResistanceSketch
open OnlineCRS.Combine (Sym)
open CFLOutliers (OutputsWithin)
open scoped Matrix.Norms.L2Operator

namespace MaxCompForest

/-- **Theorem F.1 (Greedy-pivot rational slow-response factor)**, with the polynomial bound of pp.45–46: one
machine and one absolute exponent `b`; time `(⌈γ⁻¹⌉ + L + 2)^b`, where `L` contains `q` and the bits of `θ`. The
output length is at most a constant times the time, which gives (F.19)–(F.20).
Chao–Ma–Gao–Cen–Wang, *Maximum-Completion Forests via Sharp Spectral Quantization*, STOC 2027 submission manuscript (sha256 48edea42…83e2), p.42, pp.45–46; the certified interval is Lemma F.3's, `τ = γ/(16q)`, p.42.

**Formalization Note.** The norm is the `ℓ²` operator norm (`Matrix.Norms.L2Operator`). A rank `r = 0` factor is
the empty `Fin 0 → …`. -/
theorem theorem_F_1 :
    ∃ (M : Turing.TM2ComputableAux Sym Sym) (b : ℕ),
      ∀ (I : RInst) (q : ℕ) (γ θ : ℚ), I.graph.IsConnected → 1 ≤ q → q < I.n →
        0 < γ → γ ≤ 1 → 0 < θ → θ ≤ 1 → (γ : ℝ) ≤ lam I.graph (deg I.graph) q →
        ∃ (c : ℚ) (r : ℕ) (F : Fin r → Fin I.n → ℚ),
          γ / 4 ≤ c ∧ c ≤ γ / 2 ∧
          (∀ j, j < I.n → lam I.graph (deg I.graph) j ∉
            Set.Icc (((c - γ / (16 * q) : ℚ)) : ℝ) ((c + γ / (16 * q) : ℚ) : ℝ)) ∧
          r = slowCount I.graph (c : ℝ) ∧ r + 1 ≤ q ∧
          ‖featGram (ratFeat F) - slowResp I.graph (c : ℝ)‖ ≤ (θ : ℝ) / dmax I.graph ∧
          OutputsWithin M (encFactorIn I q γ θ) (encFactorOut c r F)
            ((⌈γ⁻¹⌉₊ + (encFactorIn I q γ θ).length + 2) ^ b) := by sorry

end MaxCompForest
