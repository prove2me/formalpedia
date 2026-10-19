-- Prove2me | Theorems.Thm_GreenTao_linear_forms_cs_moments
-- name    : GreenTao.linear_forms_cs_moments
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:19:18.92004+00:00
-- url     : https://prove2.me/theorems/d3b9c04c-ccf6-47d0-ab7b-cb173fea7ed0
-- title:
--   Linear-forms estimates for progression Cauchy–Schwarz factors and cube weights
-- statement:
--   Let $d\ge2$, let $M_n$ be primes tending to infinity, and let $\mu_n\ge0$ satisfy the $((d+1)2^d,3(d+1)-4,d+1)$ linear-forms condition. For each fixed distinguished position $j\in\{0,\ldots,d\}$, the explicit progression Cauchy–Schwarz factor and cube weight satisfy
--
--   $$P_n\longrightarrow1,$$
--
--   and, for $q=0,1,2$,
--
--   $$\mathbb E_{x,h}W_n(x,h)^q\prod_{\omega\in\{0,1\}^d}\mu_n(x+\omega\cdot h)\longrightarrow1.$$
--
--   The factor $P_n$ and weight $W_n$ are those in the existing progression-CS definitions, with $W_n$ reparameterized by the progression difference. These are exactly the normalization and moment inputs needed after the finite Cauchy–Schwarz bound. No correlation-condition hypothesis is imposed.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 proof of Proposition 5.3, the assertion P_d=1+o(1) preceding equation (5.24), and Lemma 5.5 with its q=0,1,2 moment expansion. The three moment computations are evaluated in the equivalent progression-difference coordinates used by the project’s csWeight.

import Definitions.Def_GreenTao_ProgressionCS
open scoped BigOperators Topology
open Filter

theorem GreenTao.linear_forms_cs_moments
    (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+)
    (hprime : ∀ n, Nat.Prime (M n : ℕ))
    (hM : Tendsto (fun n => (M n : ℕ)) atTop atTop)
    (μ : GreenTao.Family M) (hμ : ∀ n x, 0 ≤ μ n x)
    (hLF : GreenTao.LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) :
    Tendsto (fun n => GreenTao.csFactor d j (μ n)) atTop (𝓝 1) ∧
      ∀ q : ℕ, q ≤ 2 →
        Tendsto (fun n => GreenTao.avg fun x =>
          GreenTao.avg fun h : Fin d → ZMod (M n : ℕ) =>
            GreenTao.csWeight d j (μ n) x h ^ q *
              ∏ ω : Fin d → Bool, μ n (x + ∑ i : Fin d, if ω i then h i else 0))
          atTop (𝓝 1) := by sorry
