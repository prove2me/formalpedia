-- Prove2me | Theorems.Thm_OTCChain_Equilibrium_theorem_1
-- name    : OTCChain.Equilibrium.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:25:42.416308+00:00
-- url     : https://prove2.me/theorems/ba9398b6-7f58-483e-9dd9-456a53292c18
-- title:
--   Theorem 1, p. 13 (PDF 16), corrected — for 0 < c < c*, a unique steady-state intermediation equilibrium: cutoffs solve (20)–(21), densities (55)–(63), trade iff x > y, values (79)–(82)
-- statement:
--   Consider the OTC market of the model with its standing assumptions ($0 < X < N$, $\lambda, \kappa, r > 0$, $\eta \in (0,1)$, $\bar\Delta > 0$, $f$ a probability density on $[0,\bar\Delta]$ with c.d.f. $F$), and let the search cost satisfy
--   $$0 < c < c^*,$$
--   where $c^*$ is the threshold (84). Then:
--
--   1. the equation (20), $c = \mathrm{rhs}_{20}(\Delta_b)$, has a unique solution $\Delta_b \in [0,\bar\Delta]$, and (21), $c = \mathrm{rhs}_{21}(\Delta_s)$, has a unique solution $\Delta_s \in [0,\bar\Delta]$, where $N_b$ and $N_s$ in (20), (21) are given by (66) and (64);
--   2. a steady-state intermediation equilibrium (Definition 1) exists;
--   3. every steady-state intermediation equilibrium $(\Delta_b,\Delta_s,\mu,V)$ satisfies:
--      - $\Delta_b$ solves (20) and $\Delta_s$ solves (21), and its populations are $N_b = N_b(F(\Delta_b))$ (66), $N_s = N_s(F(\Delta_s))$ (64);
--      - its densities $(\mu_b,\mu_s,\mu_n,\mu_h)$ are given by (55)–(63), with (59)–(60) corrected, at every type $\Delta \in [0,\bar\Delta]$ other than $\Delta_b$ and $\Delta_s$;
--      - its value functions $V(0,\cdot)$ and $V(1,\cdot)$ are given by (79)–(82) on $[0,\bar\Delta]$;
--      - a type-$x$ buyer ($x \in (\Delta_b,\bar\Delta]$) and a type-$y$ seller ($y \in [0,\Delta_s)$) who meet agree to trade if and only if $x > y$, and then at the price (6), $P(x,y) = V(1,x) - V(0,x) - \eta S(x,y)$, with $V$ given by (79)–(82).
--
--   In particular the equilibrium is unique: any two equilibria have the same cutoffs, the same densities off the cutoffs, and the same value functions and prices. Investors with types in $(\Delta_b,\Delta_s)$ are the intermediaries: they search to buy when they hold no asset and search to sell as soon as they hold one.
--
--   **Formalization Note** Three departures from the printed statement, all disclosed. (i) The hypothesis $c > 0$ is added: at $c = 0$, (20) forces $\int_0^{\Delta_b}F = 0$, which contradicts $\Delta_b > 0$ in Definition 1 when $f > 0$ near $0$ and gives a continuum of cutoffs when $F$ vanishes on an interval, so the printed statement fails there. (ii) The densities (59)–(60) are the corrected ones (see the milestone `eq_59_60_corrected`); (9) and (11) are read as on p. 39. (iii) The steady-state equations leave the densities free at the two cutoffs, so their uniqueness is stated off $\{\Delta_b,\Delta_s\}$. The threshold $c^*$ is a definition built from (20)–(21), not a parameter. The equilibrium predicate is Definition 1 (flow equations, Bellman system, optimality), not the closed forms; the closed forms are what the theorem proves every equilibrium equals.
-- source:
--   Shen, Wei & Yan, Financial Intermediation Chains in an OTC Market, MPRA Paper No. 74925 (version of October 29, 2016), p. 13 (PDF 16), Theorem 1

import Mathlib
import Definitions.Def_OTCChain_Equilibrium_Model
import Definitions.Def_OTCChain_Equilibrium_ClosedForm

namespace OTCChain.Equilibrium

open Set

/-- Theorem 1, p. 13 (corrected: `0 < c` added; (59)–(60) corrected; (9), (11) as on p. 39).
If `0 < c < c*`, with `c*` from (84):
1. (20) and (21) each have a unique solution in `[0, ∆̄]`;
2. a steady-state intermediation equilibrium (Definition 1) exists;
3. every such equilibrium `(∆b, ∆s, μ, V)` has `∆b` solving (20) and `∆s` solving (21), with
   `N_b`, `N_s` given by (66), (64); its densities equal (55)–(63) (with the corrected
   (59)–(60)) at every type in `[0, ∆̄]` other than the two cutoffs; its value functions
   `V(0, ·)`, `V(1, ·)` are (79)–(82) on `[0, ∆̄]`; a type-`x` buyer (`x ∈ (∆b, ∆̄]`) and a
   type-`y` seller (`y ∈ [0, ∆s)`) trade iff `x > y`, at the price (6) computed from (79)–(82). -/
theorem theorem_1 (M : Params) (hM : M.Standing) (hc : 0 < M.c) (hcs : M.c < cStar M) :
    (∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs20 M δ = M.c) ∧
    (∃! δ, δ ∈ Icc 0 M.Δbar ∧ rhs21 M δ = M.c) ∧
    (∃ (Δb Δs : ℝ) (μ : Densities) (V : Values), IsIntermEq M Δb Δs μ V) ∧
    ∀ (Δb Δs : ℝ) (μ : Densities) (V : Values), IsIntermEq M Δb Δs μ V →
      rhs20 M Δb = M.c ∧ rhs21 M Δs = M.c ∧
      μ.Nb M = NbOf M (M.F Δb) ∧ μ.Ns M = NsOf M (M.F Δs) ∧
      (∀ Δ ∈ Icc 0 M.Δbar, Δ ≠ Δb → Δ ≠ Δs →
        μ.μb Δ = (candDensities M Δb Δs).μb Δ ∧ μ.μs Δ = (candDensities M Δb Δs).μs Δ ∧
        μ.μn Δ = (candDensities M Δb Δs).μn Δ ∧ μ.μh Δ = (candDensities M Δb Δs).μh Δ) ∧
      (∀ Δ ∈ Icc 0 M.Δbar, V.V0 Δ = candV0 M Δb Δs Δ ∧ V.V1 Δ = candV1 M Δb Δs Δ) ∧
      (∀ x ∈ Ioc Δb M.Δbar, ∀ y ∈ Ico 0 Δs,
        (0 < surplus V x y ↔ y < x) ∧
        (y < x → price M V x y = candV1 M Δb Δs x - candV0 M Δb Δs x
          - M.η * (candV1 M Δb Δs x + candV0 M Δb Δs y
            - (candV0 M Δb Δs x + candV1 M Δb Δs y)))) := by sorry

end OTCChain.Equilibrium
