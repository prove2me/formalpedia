-- Prove2me | Theorems.Thm_GaussDiffSVP_corollary_4_6
-- name    : GaussDiffSVP.corollary_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:03:12.100199+00:00
-- url     : https://prove2.me/theorems/ec7fe57c-3b3c-4e86-83ed-9ebc7ef2a71c
-- title:
--   Corollary 4.6 — a balanced isolated tree has root error $B_t = 2^t\varepsilon_t + 4\sum_j2^{j-1}(\eta_j+\theta_j)$
-- statement:
--   Consider a balanced isolated tree of depth $t$, leaves at level $t$ and root at level $0$. Suppose its activation probabilities are valid ($q = cK\le1$, pairwise independent coins) and at every level $j\in\{1,\dots,t\}$ the closure and degree assumptions of Corollary 4.5 hold: with $\lambda_d = \Phi_q(\nu_j(\text{left child}),\nu_j(\text{right child}))$,
--   $$(1-\eta_j)\nu_{j-1}\le\mathbb E_d[\lambda_d]\le(1+\eta_j)\nu_{j-1},\qquad\mathbb E_d[\lambda_d^{\otimes2}]\le(1+\eta_j)^2\nu_{j-1}^{\otimes2},$$
--   and the degree bound $\theta\le\theta_j$ uniformly over $d$, with $\eta_j,\theta_j\in[0,1/4]$. If every leaf lies in $\mathcal C(\nu_t,\varepsilon_t)$ and
--   $$B_t = 2^t\varepsilon_t+4\sum_{j=1}^t2^{j-1}(\eta_j+\theta_j)\le\frac1{20},$$
--   then every root lies in $\mathcal C(\nu_0,B_t)$.
--
--   Differences from the source:
--   - generalization: the paper's tree (offsets, half-grid shifts, differences) → arbitrary offset and shift types, shift laws, child-offset maps and pair map; reason: the corollary's proof uses only these; the cooling tree is an instance
--   - reading: the closure and degree assumptions of Corollary 4.5 → (33) and $\theta\le\theta_j$ at every level; Corollary 4.5's $D\le1/10$ is not assumed; reason: it follows from (35) along the induction
--   - encoding: condition on the prescribed node offset or on the complete environment → node laws given their offsets; the complete-environment convention is the case of point-mass shift laws; reason: same convention throughout the tree
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Corollary 4.6, p.26; Corollary 4.5, p.25

import Mathlib
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_transport1
import Definitions.Def_GaussDiffSVP_IsCoinKernel
import Definitions.Def_GaussDiffSVP_isoTreeLaw

open scoped ENNReal

namespace GaussDiffSVP

/-- Corollary 4.6 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.26), with the per-level hypotheses of Corollary 4.5 (p.25). Consider a
balanced isolated tree of depth `t` (`isoTreeLaw`), leaves at level `t`, root at level `0`. At every
level `j ∈ {1, …, t}` (children at level `j`, parent at level `j − 1` with offset `p`, local shift
`d ∼ ω_{j−1}(p)`, child offsets `f_L(p, d)`, `f_R(p, d)`):

* the activation probabilities are valid: `q_{j,p,d} = c_{j,p,d} K_{j,p,d} ≤ 1`, realized by
  pairwise independent coins;
* closure (33): with `λ_d = Φ_{q_{j,p,d}}(ν_j(f_L(p,d)), ν_j(f_R(p,d)))`,
  `(1 − η_j)ν_{j−1}(p) ≤ E_d[λ_d] ≤ (1 + η_j)ν_{j−1}(p)` and
  `E_d[λ_d^{⊗2}] ≤ (1 + η_j)²ν_{j−1}(p)^{⊗2}`;
* degree: `θ = c(D⁺ + D⁻) ≤ θ_j` uniformly over `d` (Proposition 4.4's `θ`);

with `η_j, θ_j ∈ [0, 1/4]`. If every leaf lies in `C(ν_t(p), ε_t)` and
`B_t = 2^t ε_t + 4 ∑_{j=1}^t 2^{j−1}(η_j + θ_j) ≤ 1/20` (35), then every root lies in
`C(ν_0(p), B_t)`.

**Formalization Note.** The convention is "condition on the prescribed node offset": every law is
the law given its node's offset, and the shift average is `E_d` under `ω`. The complete-environment
convention is the special case of point-mass shift laws. Corollary 4.5's input hypothesis
`D ≤ 1/10` is not an assumption of Corollary 4.6: it follows from (35) along the induction. -/
theorem corollary_4_6 {α O D : Type*} (t : ℕ) (T : α → α → α) (ω : ℕ → O → PMF D)
    (fL fR : O → D → O) (c : ℕ → O → D → ℝ≥0∞) (K : ℕ → O → D → α → α → ℝ≥0∞)
    (κ : ℕ → O → D → (lL : List α) → (lR : List α) → PMF (Fin lL.length × Fin lR.length → Bool))
    (hκ : ∀ j, 1 ≤ j → j ≤ t → ∀ p d, (∀ x y, c j p d * K j p d x y ≤ 1) ∧
      IsCoinKernel (fun x y => c j p d * K j p d x y) (κ j p d))
    (leaf : O → PMF (List α)) (ν : ℕ → O → α → ℝ≥0∞) (εt : ℝ) (η θ : ℕ → ℝ)
    (hηθ : ∀ j, 1 ≤ j → j ≤ t → 0 ≤ η j ∧ η j ≤ 1 / 4 ∧ 0 ≤ θ j ∧ θ j ≤ 1 / 4)
    (hleaf : ∀ p, InClassC (leaf p) (ν t p) εt)
    (h33 : ∀ j, 1 ≤ j → j ≤ t → ∀ p,
      (∀ z, ENNReal.ofReal (1 - η j) * ν (j - 1) p z ≤ ∑' d, ω (j - 1) p d *
          transport1 T (fun x y => c j p d * K j p d x y) (ν j (fL p d)) (ν j (fR p d)) z ∧
        ∑' d, ω (j - 1) p d *
          transport1 T (fun x y => c j p d * K j p d x y) (ν j (fL p d)) (ν j (fR p d)) z ≤
          ENNReal.ofReal (1 + η j) * ν (j - 1) p z) ∧
      ∀ z z', ∑' d, ω (j - 1) p d *
          (transport1 T (fun x y => c j p d * K j p d x y) (ν j (fL p d)) (ν j (fR p d)) z *
            transport1 T (fun x y => c j p d * K j p d x y) (ν j (fL p d)) (ν j (fR p d)) z') ≤
        ENNReal.ofReal ((1 + η j) ^ 2) * (ν (j - 1) p z * ν (j - 1) p z'))
    (hdeg : ∀ j, 1 ≤ j → j ≤ t → ∀ p d,
      c j p d * ((⨆ x, ∑' y, K j p d x y * ν j (fR p d) y) +
        (⨆ y, ∑' x, K j p d x y * ν j (fL p d) x)) ≤ ENNReal.ofReal (θ j))
    (h35 : (2 : ℝ) ^ t * εt + 4 * ∑ j ∈ Finset.Icc 1 t, (2 : ℝ) ^ (j - 1) * (η j + θ j) ≤ 1 / 20) :
    ∀ p, InClassC (isoTreeLaw t T ω fL fR κ leaf t p) (ν 0 p)
      ((2 : ℝ) ^ t * εt + 4 * ∑ j ∈ Finset.Icc 1 t, (2 : ℝ) ^ (j - 1) * (η j + θ j)) := by sorry

end GaussDiffSVP
