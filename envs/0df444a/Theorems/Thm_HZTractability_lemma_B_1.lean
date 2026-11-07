-- Prove2me | Theorems.Thm_HZTractability_lemma_B_1
-- name    : HZTractability.lemma_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:08:57.539813+00:00
-- url     : https://prove2.me/theorems/a5c00f28-9000-4914-b69a-b5569a988b6b
-- title:
--   Lemma B.1 — allocated slack and demand deficits
-- statement:
--   Let $(p,x)$ be a normalized additive $\varepsilon$-equilibrium, $\varepsilon\ge0$, of an HZ market with utilities in $[0,1]$. For buyer $i$, let $E^+_i$ and $E^0_i$ be her expenditure on goods with $u_{ij}>0$ and with $u_{ij}=0$, and $Q^0_i$ her total quantity of goods with $u_{ij}=0$. Let $(\beta_i,\mu_i)$ be an optimal demand dual: $\beta_i\ge0$, $\beta_ip_j+\mu_i\ge u_{ij}$, $\beta_i+\mu_i=V_i(p)$. Then:
--
--   1. $0\le\beta_i,\mu_i\le1$;
--   2. her allocated reduced slack satisfies (31):
--   $$
--   \sum_j(\beta_ip_j+\mu_i-u_{ij})x_{ij}=V_i(p)-U_i(x_i)+\beta_i(p\cdot x_i-1)\le2\varepsilon ;
--   $$
--   3. if $\beta_i>0$, then $E^0_i\le2\varepsilon/\beta_i$ and $1-\varepsilon/\beta_i\le E^+_i\le1+\varepsilon$;
--   4. if $\mu_i>0$, then $Q^0_i\le2\varepsilon/\mu_i$;
--   5. for a population of $M$ identical buyers using one common optimal dual $(\beta,\mu)$, a group with price $p$ and reduced slack $s=\beta p+\mu-u_{ij}>0$ receives at most $2M\varepsilon/s$ quantity and $2M\varepsilon p/s$ expenditure from the population.
--
--   The lemma converts the equilibrium error into bounds on spending away from optimal goods.
--
--   Differences from the source:
--   - generalization: the market of Section 3 with prices equalized within each group → any finite HZ market with utilities in $[0,1]$ and any $\varepsilon\ge0$; reason: the proof uses only normalization and $u_{ij}\in[0,1]$; the market of §3 with equalized prices is an instance
--   - encoding: a population of $M$ identical buyers using one common optimal dual, a group with reduced slack $s>0$ and price $p$ → a finite set $P$ of buyers with identical utility rows, each with the optimal dual $(\beta,\mu)$, and a set $S$ of goods of common price $p$ with $\beta p_j+\mu-u_{ij}=s$ for $i\in P$, $j\in S$; $M=|P|$; reason: same objects
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Lemma B.1, p.38 (PDF p.40)

import Mathlib
import Definitions.Def_HZTractability_IsNormAddEq
import Definitions.Def_HZTractability_IsOptDual

namespace HZTractability

/-- **Lemma B.1 (Allocated slack and demand deficits)** (Panageas–Shein–Taherijam–Vazirani,
arXiv:2610.35848, held version, sha256 74b7bf9f…, p.38 (PDF 40)), for any HZ market with utilities
in `[0, 1]` and any normalized additive ε-equilibrium `(x, p)`, `ε ≥ 0`.

For a buyer `i` and an optimal demand dual `(β, μ)` (`β ≥ 0`, `β p_j + μ ≥ u_ij`, `β + μ = V_i(p)`):
1. `0 ≤ β, μ ≤ 1`;
2. (31): `∑_j (β p_j + μ − u_ij) x_ij = V_i(p) − U_i(x_i) + β(p · x_i − 1) ≤ 2ε`;
3. if `β > 0`: `E⁰_i ≤ 2ε/β` and `1 − ε/β ≤ E⁺_i ≤ 1 + ε`, where `E⁺_i`, `E⁰_i` are her expenditure
   on goods with `u_ij > 0` and with `u_ij = 0`;
4. if `μ > 0`: `Q⁰_i ≤ 2ε/μ`, her total quantity of goods with `u_ij = 0`;
5. for a population `P` of `M` identical buyers using one common optimal dual `(β, μ)`, a group `S`
   with common price `p` and reduced slack `s = β p + μ − u_ij > 0` receives at most `2Mε/s` quantity
   and `2Mεp/s` expenditure from `P`.

**Formalization Note** The paper states the lemma for the market of §3; its proof uses only
normalization and utilities in `[0, 1]`, and it is stated here for every such market. -/
theorem lemma_B_1 {B G : Type} [Fintype B] [Fintype G] (u : B → G → ℝ)
    (hu : ∀ i j, 0 ≤ u i j ∧ u i j ≤ 1) (ε : ℝ) (hε : 0 ≤ ε) (x : B → G → ℝ) (p : G → ℝ)
    (heq : IsNormAddEq u ε x p) :
    (∀ (i : B) (β μ : ℝ), IsOptDual u p i β μ →
      (0 ≤ β ∧ β ≤ 1 ∧ 0 ≤ μ ∧ μ ≤ 1) ∧
      ∑ j, (β * p j + μ - u i j) * x i j =
        (β + μ) - ∑ j, u i j * x i j + β * (∑ j, p j * x i j - 1) ∧
      ∑ j, (β * p j + μ - u i j) * x i j ≤ 2 * ε ∧
      (0 < β →
        (∑ j, if u i j = 0 then p j * x i j else 0) ≤ 2 * ε / β ∧
        1 - ε / β ≤ (∑ j, if 0 < u i j then p j * x i j else 0) ∧
        (∑ j, if 0 < u i j then p j * x i j else 0) ≤ 1 + ε) ∧
      (0 < μ → (∑ j, if u i j = 0 then x i j else 0) ≤ 2 * ε / μ)) ∧
    ∀ (P : Finset B) (S : Finset G) (β μ s pr : ℝ),
      (∀ i ∈ P, ∀ i' ∈ P, u i = u i') → (∀ i ∈ P, IsOptDual u p i β μ) →
      (∀ j ∈ S, p j = pr) → 0 < s → (∀ i ∈ P, ∀ j ∈ S, β * p j + μ - u i j = s) →
      ∑ i ∈ P, ∑ j ∈ S, x i j ≤ 2 * P.card * ε / s ∧
      ∑ i ∈ P, ∑ j ∈ S, p j * x i j ≤ 2 * P.card * ε * pr / s := by sorry

end HZTractability
