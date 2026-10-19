-- Prove2me | Theorems.Thm_GreenTao_linear_forms_cs_weight_moments
-- name    : GreenTao.linear_forms_cs_weight_moments
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-16T21:29:55.309811+00:00
-- url     : https://prove2.me/theorems/7f3497dc-f246-43a5-995d-d73338d181d1
-- title:
--   Linear-forms condition gives the first two positive cube-weight moments
-- statement:
--   Let $d\ge2$ and let $\mu_n$ satisfy the $((d+1)2^d,3(d+1)-4,d+1)$ linear-forms condition. Fix a distinguished progression position $j$. For $q=1,2$, the explicit progression cube weight satisfies
--
--   $$\mathbb E_{x,h}W_n(x,h)^q\prod_{\omega\in\{0,1\}^d}\mu_n(x+\omega\cdot h)\longrightarrow1.$$
--
--   Here $W_n$ is the weight in the progression-CS definitions, expressed using the progression difference. This supplies the positive moments in the proof that the majorant covers its cubes uniformly. Only the existing linear-forms condition is required; no additional primality, growth, nonnegativity, or correlation-condition assumption is used. The zero moment is the separately proved normalization of the cube average.
-- source:
--   Green and Tao, The primes contain arbitrarily long arithmetic progressions, https://arxiv.org/html/math/0404188v6, §5 Lemma 5.5, q=1 and q=2 moment computations. The proof uses the equivalent progression-difference coordinates in csWeight: a cube row and one or two copies of the face forms x+c_i r+Σ_l(1−c_i/c_l)ω_l h_l, with ω_i=0.

import Definitions.Def_GreenTao_ProgressionCS
open scoped BigOperators Topology
open Filter GreenTao

theorem GreenTao.linear_forms_cs_weight_moments (d : ℕ) (hd : 2 ≤ d) (M : ℕ → ℕ+) (μ : Family M)
    (hLF : LinearFormsCondition M μ ((d + 1) * 2 ^ d) (3 * (d + 1) - 4) (d + 1))
    (j : Fin (d + 1)) (q : ℕ) (hq₀ : 1 ≤ q) (hq₂ : q ≤ 2) :
    Tendsto (fun n => avg fun x => avg fun h : Fin d → ZMod (M n : ℕ) =>
      csWeight d j (μ n) x h ^ q *
        ∏ ω : Fin d → Bool, μ n (x + ∑ a : Fin d, if ω a then h a else 0)) atTop (𝓝 1) := by sorry
