-- Prove2me | Theorems.Thm_HoneycombCodes_eq_45
-- name    : HoneycombCodes.eq_45
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:30:37.383039+00:00
-- url     : https://prove2.me/theorems/6d274d08-fb1c-4738-b7d5-121177ddf8eb
-- title:
--   Equation (45) — half-spin Racah factors converge to $P$ and $1-P$
-- statement:
--   Along the scaling $i/n\to x$, $j/(n-i)\to\eta$, $\ell/i\to\rho$, $k/n\to z$, the squared Racah factors of the box-transfer edges satisfy, uniformly on compact subsets of the strict triangle region (49),
--
--   $$
--   R^2_{\sigma\tau}\longrightarrow\begin{cases}P,&\sigma=\tau,\\ 1-P,&\sigma\ne\tau,\end{cases}
--   $$
--
--   where $P=(E^2-(A-B)^2)/(4AB)$ is (5). Concretely: for every compact set $K$ inside the strict region and every $\varepsilon>0$ there is $N$ such that for all $n\ge N$, all $k$, all triples $(i,j,\ell)$ and all $\sigma,\tau\in\{0,1\}$ whose normalized point $(i/n,\ j/(n-i),\ \ell/i,\ k/n)$ lies in $K$, the factor $R^2_{\sigma\tau}$ is within $\varepsilon$ of $P$ (if $\sigma=\tau$) or of $1-P$ (if $\sigma\ne\tau$), with $P$ evaluated at that normalized point.
--
--   Combined with the Specht removal ratios this gives the limiting edge weights (46), whose doubled sum is $\Gamma_{HC}$.
--
--   Differences from the source:
--
--   - reading: 'uniformly on compact subsets of the strict triangle region' → for every compact K in the strict region (49) and ε > 0, an N with |R²_{στ} − P| ≤ ε (σ = τ), |R²_{στ} − (1 − P)| ≤ ε (σ ≠ τ) at every n ≥ N and every (i, j, ℓ, k) whose normalized point lies in K; reason: the standard meaning of locally uniform convergence along the scaling (41), and the form Lemma 5.1 Step 2 uses
--   - generalization: valid triples of the box-transfer graph → all triples (i, j, ℓ) and all k whose normalized point lies in K; reason: the limit is a statement about the closed form R²_{στ}; valid triples are among the quantified ones, so it specializes to the source's
--   - reading: contraction coefficients p_{ω,ω′} 'using Theorem 4.4' (squared 6j symbols, Racah factor R²_{στ}) → the closed forms (32)–(33) with R²_{σσ} = Q_σ, R²_{σ,1−σ} = 1 − Q_σ from Remark 4.7 and (117), set to 0 when an endpoint is not valid; reason: Remark 4.7 and App. A.2 identify the squared Racah factors with this closed form, which is what the paper computes with
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §5, eq. (45), p.25 (PDF 27); proof App. A.2, pp.53–54 (PDF 55–56)

import Mathlib
import Definitions.Def_HoneycombCodes_pDir
import Definitions.Def_HoneycombCodes_kappaHC

set_option autoImplicit false

namespace HoneycombCodes

/-- **Equation (45)** (the half-spin Racah limit), Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.25 (PDF 27); proof App. A.2,
pp.53–54. Uniformly on compact subsets of the strict triangle region (49),
`R²_{στ} → P` for `σ = τ` and `R²_{στ} → 1 − P` for `σ ≠ τ`, where `P` is (5) at the
normalized point `(i/n, j/(n − i), ℓ/i, k/n)` of the scaling (41).

**Formalization Note (reading).** "Uniformly on compact subsets of the strict region": for every
compact `K` contained in the strict region (49) and every `ε > 0` there is `N` such that for all
`n ≥ N`, all `k`, all triples `(i, j, ℓ)` and all `σ, τ` whose normalized point lies in `K`,
`|R²_{στ} − P| ≤ ε` (`σ = τ`) and `|R²_{στ} − (1 − P)| ≤ ε` (`σ ≠ τ`), with `P` evaluated at
that normalized point. `R²_{στ}` is the closed form of Remark 4.7 (`R2coef`). Divisions are real. -/
theorem eq_45 (K : Set (ℝ × ℝ × ℝ × ℝ)) (hK : IsCompact K)
    (hKstrict : ∀ q ∈ K, InStrictHC q.1 q.2.1 q.2.2.1 q.2.2.2) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ (k : ℕ) (ω : ℕ × ℕ × ℕ) (σ τ : Fin 2),
      ((ω.1 : ℝ) / n, (ω.2.1 : ℝ) / ((n : ℝ) - ω.1), (ω.2.2 : ℝ) / ω.1, (k : ℝ) / n) ∈ K →
      |R2coef n k σ τ ω -
          (if σ = τ then
            PHC ((ω.1 : ℝ) / n) ((ω.2.1 : ℝ) / ((n : ℝ) - ω.1)) ((ω.2.2 : ℝ) / ω.1) ((k : ℝ) / n)
          else
            1 - PHC ((ω.1 : ℝ) / n) ((ω.2.1 : ℝ) / ((n : ℝ) - ω.1)) ((ω.2.2 : ℝ) / ω.1)
              ((k : ℝ) / n))| ≤ ε := by sorry

end HoneycombCodes
