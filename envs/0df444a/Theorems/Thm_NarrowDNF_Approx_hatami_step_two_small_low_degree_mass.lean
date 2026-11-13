-- Prove2me | Theorems.Thm_NarrowDNF_Approx_hatami_step_two_small_low_degree_mass
-- name    : NarrowDNF.Approx.hatami_step_two_small_low_degree_mass
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-12T10:13:33.082911+00:00
-- url     : https://prove2.me/theorems/46d29971-eeab-4c4b-8f1b-f481053dda1e
-- title:
--   Hatami (11), Bourgain's step — small low-degree Walsh mass below the threshold ε₁ = exp(−1000k²)
-- statement:
--   Let $0 < p \le 1/2$, let $f : \{0,1\}^n \to \{0,1\}$, let $C \ge 1$ be a natural number with $I_p(f) \le C$, where $I_p$ is the total resampling influence (`FriedgutCoalition.totalPInfl`, Hatami's eq. (9)), and let $0 < \varepsilon_0 \le 10^{-3}$. Put $k = C/\varepsilon_0$ (a real number, not rounded) and $\varepsilon_1 = \exp(-1000k^2)$.
--
--   Write the $p$-biased Walsh expansion $f = \sum_S F_S$ with $F_S(x) = \hat f(S)\prod_{i\in S} r(x_i)$, where $r(1) = \sqrt{(1-p)/p}$, $r(0) = -\sqrt{p/(1-p)}$ and $\hat f(S) = \mathbb E_p\big[f \cdot \prod_{i\in S} r(x_i)\big]$. Then
--   $$\sum_{|S| \le k} \mathbb E_p\big[F_S^2\,\mathbf 1[|F_S| \le \varepsilon_1]\big] \le \frac{\varepsilon_0}{k}.$$
--
--   This is the middle inequality of Hatami's (11) (Step II of the proof of Hatami's Theorem 2.8, obtained there from Bourgain's argument in the appendix to Friedgut's 1999 paper), with $C = \lceil I_p(f)\rceil$ relaxed to any natural $C \ge I_p(f)$, $C \ge 1$, and with Hatami's truncation level $3^{-10k^2}\varepsilon_0^{10k}$ replaced by the smaller $\exp(-1000k^2)$. Since $k \ge 1/\varepsilon_0$, Hatami's level is at least $\exp(-21k^2)$, and the left-hand side only shrinks as $\varepsilon_1$ decreases, so this statement is implied by Hatami's. Expectations are exact finite sums over the cube under the $p$-biased product weights.
--
--   It is the only non-elementary input of `NarrowDNF.Approx.lemma_2_1` (Hatami's construction with arity and load): a proof of that lemma from this statement, covering Steps I, III and IV, has been submitted.
-- source:
--   H. Hatami, A structure theorem for Boolean functions with small total influences, Ann. of Math. 176 (2012), 509–533, https://doi.org/10.4007/annals.2012.176.1.9, Section 4.2 (Step II, Bourgain’s argument), inequality (11), in the weaker form with the smaller truncation level exp(-1000k^2); arXiv:1008.1021v3, p. 8

import Definitions.Def_NarrowDNF_Approx_Probability

namespace NarrowDNF.Approx

theorem hatami_step_two_small_low_degree_mass {n : ℕ} (p : ℝ) (f : Cube n → Bool)
    (hp : 0 < p) (hp_half : p ≤ 1 / 2) (C : ℕ) (hC : 1 ≤ C)
    (hI : FriedgutCoalition.totalPInfl p f ≤ C) (ε₀ : ℝ) (hε₀ : 0 < ε₀)
    (hε₀_le : ε₀ ≤ 1 / 1000) :
    let k : ℝ := C / ε₀
    let ε₁ : ℝ := Real.exp (-(1000 * k ^ 2))
    let r : Bool → ℝ := fun b => if b then Real.sqrt ((1 - p) / p) else -Real.sqrt (p / (1 - p))
    let F : Finset (Fin n) → Cube n → ℝ := fun S x =>
      expect p (fun y => (if f y then 1 else 0) * ∏ i ∈ S, r (y i)) * ∏ i ∈ S, r (x i)
    ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => (S.card : ℝ) ≤ k),
      expect p (fun x => if |F S x| ≤ ε₁ then F S x ^ 2 else 0) ≤ ε₀ / k := by sorry

end NarrowDNF.Approx
