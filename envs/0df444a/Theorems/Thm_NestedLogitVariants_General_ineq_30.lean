-- Prove2me | Theorems.Thm_NestedLogitVariants_General_ineq_30
-- name    : NestedLogitVariants.General.ineq_30
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:42:46.36922+00:00
-- url     : https://prove2.me/theorems/c6535176-772d-4193-9021-2b51054765b4
-- title:
--   Inequality (30), A.4 Case 1, p. 47 — β ŷ_i bounds the relaxed objective at every fractional prefix
-- statement:
--   Let the instance satisfy the standing assumptions with $\bar\gamma>1$, let $\beta$ be the factor (12), and let $(\hat x,\hat y)$ be an optimal solution of (4) with the collection $\{N^k_{ij}\}\cup\{\{j\}\}$ in every nest. Fix a nest $i$ with $\gamma_i>1$ and $\hat y_i\ge0$. Write $R_{ik'}=\sum_{j=1}^{k'}r_{ij}v_{ij}$ and $q_{ik'}=\sum_{j=1}^{k'}v_{ij}$. Then for every product $k\in\{1,\dots,n\}$ and every $\rho\in[0,1]$,
--   $$
--   \beta\,\hat y_i\ \ge\ (v_{i0}+q_{i,k-1}+v_{ik}\rho)^{\gamma_i}\left[\frac{R_{i,k-1}+r_{ik}v_{ik}\rho}{v_{i0}+q_{i,k-1}+v_{ik}\rho}-\beta\,\hat x\right].
--   $$
--   This is the outer inequality of (30), proved on the page for $k\ge2$ (Case 1.a) and extended to $k=1$ in Case 1.b, both for partially-captured and for fully-captured nests. The right-hand side is the relaxed objective at the fractional-prefix vector $(1,\dots,1,\rho,0,\dots,0)$.
--
--   **Formalization Note** Products are indexed from $0$: the Lean index $k$ is the page's $k+1$, and $R_{i,k-1}$, $q_{i,k-1}$ are sums over `nbr n k`. The inequality is stated for every $\rho\in[0,1]$, as the page's derivation allows; for $v_{i0}=0$, $k=1$, $\rho=0$ both the base and the Lean value of the right-hand side are $0$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 47, Appendix A.4, Case 1.a, inequality (30), and Case 1.b

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Factor
import Definitions.Def_NestedLogitVariants_General_Relaxation

namespace NestedLogitVariants.General

/-- Inequality (30) (Appendix A.4, Case 1, p. 47), extended to `k = 1` by Case 1.b: in a nest with
`γ_i > 1` and `ŷ_i ≥ 0`, for every product `k` (here a `Fin n`; the paper's `k` is `k.val + 1`)
and every `ρ ∈ [0, 1]`,
`β ŷ_i ≥ (v_{i0} + q_{i,k−1} + v_{ik} ρ)^{γ_i} [(R_{i,k−1} + r_{ik} v_{ik} ρ)/(v_{i0} + q_{i,k−1} + v_{ik} ρ) − β x̂]`. -/
theorem ineq_30 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i) (β : ℝ) (hβ : IsGreatest (betaSet I) β)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh)
    (i : ι) (hγi : 1 < I.γ i) (hyi : 0 ≤ yh i) (k : Fin n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc 0 1) :
    (I.vnp i + qsum I i k.val + I.v i k * ρ) ^ I.γ i *
        ((Rsum I i k.val + I.r i k * I.v i k * ρ) / (I.vnp i + qsum I i k.val + I.v i k * ρ)
          - β * xh) ≤ β * yh i := by sorry

end NestedLogitVariants.General
