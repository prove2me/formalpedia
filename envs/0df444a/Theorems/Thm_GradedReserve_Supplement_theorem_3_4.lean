-- Prove2me | Theorems.Thm_GradedReserve_Supplement_theorem_3_4
-- name    : GradedReserve.Supplement.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:51:15.810843+00:00
-- url     : https://prove2.me/theorems/9dae6719-64af-4daa-bf75-bc1ee07b5c68
-- title:
--   Theorem 3.4 — all Bayes–Nash equilibria of $G_\pi$ and $\mathrm{LP}(d,\lambda)$
-- statement:
--   Let $n\ge2$ and let $F$ be absolutely continuous on $[0,1]$ with density $f>0$ almost everywhere on $(0,1)$; bidders are risk neutral, their private randomizations are independent, the exit action is available, graded-reserve auctions break ties uniformly and loser-payment auctions by the lowest index. Write $Q=F^{n-1}$, $T_\lambda=\lambda+(1-\lambda)Q$ and $m_a(v)=vQ(v)-\int_a^vQ$.
--
--   1. For every non-decreasing $\pi:[0,1]\to[0,1]$, every BNE $(\sigma_1,\dots,\sigma_n)$ of $G_\pi$, including asymmetric and mixed ones, is equivalent in interim allocation and expected payment, almost everywhere and for every bidder, to a symmetric BNE. Any two BNE of $G_\pi$ have the same interim allocations and payments (for every pair of bidders) and the same expected revenue; for almost every type that trades with positive probability, both play the same pure bid; and no bidder's bid distribution has an atom at a bid $b$ with $\pi(b)>0$. No continuity of $\pi$ is required.
--   2. For every $d\in(0,1]$ and $\lambda\in[0,1]$ there is a unique $a\in(0,1]$ with
--   $$d\,T_\lambda(a)=aQ(a);$$
--   $\mathrm{LP}(d,\lambda)$ has a symmetric BNE, and every BNE of $\mathrm{LP}(d,\lambda)$ has, for every bidder, the interim outcome
--   $$q(v)=Q(v)\mathbf 1\{v\ge a\},\qquad m(v)=m_a(v)\mathbf 1\{v\ge a\}\quad\text{a.e.},$$
--   no atoms at valid bids, and expected revenue $R_n(a)$.
--   3. In particular, on $G$ every $\tau$-admissible $G_\pi$ has revenue at least $\tau$ in every BNE, and Theorem 3.1 holds verbatim with $\tau$-admissibility strengthened to "has a BNE and every BNE yields revenue at least $\tau$": for $F(v)=v^k$ ($k\ge1$), $\varepsilon\in(0,1)$, $\tau=(1-\varepsilon)R^*>R_n(0)$, equation (3) has a unique root $p>p_{\min}$, and for this $p$ the graded reserve $\pi^*$ is admissible in this stronger sense, every graded reserve admissible in this sense has $\mathrm{Rev}_{\mathrm{anc}}(G_\pi)\le\mathrm{Rev}_{\mathrm{anc}}(G_{\pi^*})=\frac N{N+1}\big[1-b_0^{N+1}\frac p{p+N+1}\big]$, $\beta^*$ is a BNE of $G_{\pi^*}$ with $\pi^*(\beta^*(v))=s^*(v)$, every BNE of $G_{\pi^*}$ plays $\beta^*$ almost everywhere, every positive bid is accepted with positive probability, $\bar v<1$, and $s^*=1$ on $[\bar v,1]$.
--
--   The theorem removes the restriction to symmetric equilibria from the rational revenue guarantee: on graded reserves and on the loser-payment family the guarantee, and the optimality of $\pi^*$, hold for every equilibrium.
--
--   **Formalization Note** Equilibria are `IsBNE` profiles of Markov kernels, one per bidder. Part 3 restates the base mission's Theorem 3.1 with `IsTauAdmissibleAll` in place of `IsTauAdmissible`.
--
--   Differences from the source:
--   - encoding: F absolutely continuous on [0,1] with f > 0 almost everywhere on (0,1) → IsValueDensityAE f: f measurable, ≥ 0 a.e. on [0,1], > 0 a.e. on (0,1), ∫₀¹ f = 1, F(v) = ∫₀^v f; reason: an absolutely continuous F on [0,1] is exactly one with such a density; the same distributions
--   - encoding: n bidders (Section 2: n ≥ 2) → hypothesis 2 ≤ n; reason: Section 2 standing assumption
--   - encoding: mixed strategies with an exit action, independent private randomizations → one Markov kernel per bidder from values to actions in ℝ; negative actions (and actions above 1) are exit; the action profile law is the product of the bidders' action laws; reason: Lean convention; the same strategies
--   - reading: a Bayes–Nash equilibrium → IsBNE: for every bidder, almost every type (for the value law) best-responds; reason: the paper's convention, "Statements about types are understood up to F-null sets" (p.26)
--   - encoding: the tie rules of Definitions 2.3 and 4.1 → gradedMech (uniform ties: probability π(b)/#ties) and lpMech (lowest index wins ties); reason: the same mechanisms
--   - reading: is equivalent … to a symmetric BNE → there is a kernel σs that is a symmetric BNE (base IsSymBNE, and IsBNE of the constant profile) with qᵢ = q and mᵢ = m a.e. for every bidder i; reason: both notions of symmetric BNE are stated; they coincide
--   - reading: all BNE have the same interim outcome and expected revenue, their bids coincide almost everywhere on the set of types that trade with positive probability → for any two BNE σ, σ′ and bidders i, j: equal expected revenue, qᵢ^σ = q_j^σ′ and mᵢ^σ = m_j^σ′ a.e., and for a.e. type with qᵢ^σ(v) > 0 both σᵢ(v) and σ′_j(v) are the same point mass; reason: the paper's "same interim outcome" across bidders and equilibria (Lemmas B.6, B.8)
--   - reading: bids with π(b) > 0 have no atoms → every bidder's action law puts no mass on any b ∈ [0,1] with π(b) > 0; reason: the stated claim
--   - reading: every BNE of LP(d, λ) has the interim outcome of the symmetric equilibrium of Theorem 4.3(1) with the threshold a solving dTλ(a) = aQ(a) → ∃! a ∈ (0,1] with d T_λ(a) = aQ(a); a symmetric BNE of LP(d, λ) exists; every BNE has qᵢ = Q·1{v ≥ a}, mᵢ = m_a·1{v ≥ a} a.e.; reason: "the threshold a solving" and "the symmetric equilibrium" presuppose the unique root and the equilibrium; both are stated (Lemma B.9); a = 1 when d = 1
--   - reading: valid bids have no atoms, so the lowest-index tie rule plays no role → no bidder's action law has an atom at a valid bid b ∈ [d,1], b > 0; reason: the tie-rule remark is a consequence of the no-atom clause
--   - reading: on G the guarantee holds in every BNE → every τ-admissible (Definition 2.1) graded reserve has expRevenue ≥ τ in every BNE; reason: the stated claim
--   - reading: Theorem 3.1 holds verbatim with this stronger requirement → all clauses of the base GradedReserve.theorem_3_1 with IsTauAdmissibleAll (a BNE exists, every BNE has revenue ≥ τ) for admissibility, β* a BNE as a constant profile, and every BNE (not only symmetric) of G_{π*} playing β* a.e.; reason: the verbatim restatement; "the equilibrium" now ranges over all BNE
--   - encoding: F(v) = v^k, k ≥ 1, in the Theorem 3.1 clause → powerDensity k, k real; reason: as in the base mission
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Theorem 3.4, p.7 (PDF 8); proof Section B, pp.25–32 (PDF 26–33)

import Mathlib
import Definitions.Def_GradedReserve_IsGradedReserve
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_IsTauAdmissible
import Definitions.Def_GradedReserve_typeMeasure
import Definitions.Def_GradedReserve_bidLaw
import Definitions.Def_GradedReserve_oppCdf
import Definitions.Def_GradedReserve_revCurve
import Definitions.Def_GradedReserve_optRevenue
import Definitions.Def_GradedReserve_powerDensity
import Definitions.Def_GradedReserve_pMin
import Definitions.Def_GradedReserve_lhs3
import Definitions.Def_GradedReserve_piStar
import Definitions.Def_GradedReserve_bZero
import Definitions.Def_GradedReserve_powN
import Definitions.Def_GradedReserve_revAnc
import Definitions.Def_GradedReserve_betaStar
import Definitions.Def_GradedReserve_sStar
import Definitions.Def_GradedReserve_vbar
import Definitions.Def_GradedReserve_Supplement_IsValueDensityAE
import Definitions.Def_GradedReserve_Supplement_IsBNE
import Definitions.Def_GradedReserve_Supplement_interimQ
import Definitions.Def_GradedReserve_Supplement_interimM
import Definitions.Def_GradedReserve_Supplement_expRevenue
import Definitions.Def_GradedReserve_Supplement_gradedMech
import Definitions.Def_GradedReserve_Supplement_lpMech
import Definitions.Def_GradedReserve_Supplement_lpT
import Definitions.Def_GradedReserve_Supplement_lpM
import Definitions.Def_GradedReserve_Supplement_IsTauAdmissibleAll
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve.Supplement

/-- **Theorem 3.4** (All Bayes–Nash equilibria) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Theorem 3.4, p.7, PDF 8; proof Section B,
pp.25–32, PDF 26–33). Let `n ≥ 2` and let `F` be absolutely continuous on `[0, 1]` with `f > 0`
almost everywhere on `(0, 1)`, with risk-neutral bidders, independent private randomizations, the
exit action, and the tie rules of Definitions 2.3 (uniform) and 4.1 (lowest index).
1. For every non-decreasing `π`, each BNE of `G_π`, including asymmetric and mixed ones, is
   equivalent in interim allocation and expected payment, almost everywhere, to a symmetric BNE.
   All BNE of `G_π` have the same interim outcome and expected revenue, their bids coincide
   almost everywhere on the set of types that trade with positive probability, and bids with
   `π(b) > 0` have no atoms. No continuity of `π` is required.
2. For every `d ∈ (0, 1]` and `λ ∈ [0, 1]` there is a unique threshold `a ∈ (0, 1]` with
   `d T_λ(a) = a Q(a)`; `LP(d, λ)` has a symmetric BNE, every BNE of `LP(d, λ)` has the interim
   outcome `q(v) = Q(v)1{v ≥ a}`, `m(v) = m_a(v)1{v ≥ a}` of display (50), valid bids have no
   atoms, and every BNE has revenue `R_n(a)`.
In particular, on `G` the guarantee holds in every BNE, and Theorem 3.1 holds verbatim with this
stronger requirement.

**Formalization Note.** The binder `lam` is the paper's `λ`. Equilibria are `IsBNE` profiles of
Markov kernels, one per bidder. "Equivalent to a symmetric BNE" gives a kernel that is a symmetric
BNE both in the base mission's sense (`IsSymBNE`) and as a constant profile. "Bids coincide" is
read as: for almost every type with positive interim allocation, the two strategies are the same
point mass, for any two bidders and any two BNE. The final clause restates the base mission's
`GradedReserve.theorem_3_1` with `IsTauAdmissibleAll` (a BNE exists and every BNE has revenue at
least `τ`) in place of `IsTauAdmissible`, and with every BNE of `G_{π*}` (not only symmetric ones)
playing `β*` almost everywhere. -/
theorem theorem_3_4 (n : ℕ) (hn : 2 ≤ n) :
    (∀ f : ℝ → ℝ, IsValueDensityAE f →
      (∀ π : ℝ → ℝ, IsGradedReserve π → ∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (gradedMech n π) f σ →
        (∃ σs : Kernel ℝ ℝ, IsSymBNE f n π σs ∧ IsBNE (gradedMech n π) f (fun _ => σs) ∧
          ∀ i, interimQ (gradedMech n π) f σ i =ᵐ[typeMeasure f]
              interimQ (gradedMech n π) f (fun _ => σs) i ∧
            interimM (gradedMech n π) f σ i =ᵐ[typeMeasure f]
              interimM (gradedMech n π) f (fun _ => σs) i) ∧
        ∀ i, ∀ b ∈ Icc (0:ℝ) 1, 0 < π b → bidLaw f (σ i) {b} = 0) ∧
      (∀ π : ℝ → ℝ, IsGradedReserve π → ∀ σ σ' : Fin n → Kernel ℝ ℝ,
        IsBNE (gradedMech n π) f σ → IsBNE (gradedMech n π) f σ' →
        expRevenue (gradedMech n π) f σ = expRevenue (gradedMech n π) f σ' ∧
        ∀ i j, interimQ (gradedMech n π) f σ i =ᵐ[typeMeasure f]
              interimQ (gradedMech n π) f σ' j ∧
            interimM (gradedMech n π) f σ i =ᵐ[typeMeasure f]
              interimM (gradedMech n π) f σ' j ∧
            ∀ᵐ v ∂(typeMeasure f), 0 < interimQ (gradedMech n π) f σ i v →
              ∃ b : ℝ, σ i v = Measure.dirac b ∧ σ' j v = Measure.dirac b) ∧
      (∀ d ∈ Ioc (0:ℝ) 1, ∀ lam ∈ Icc (0:ℝ) 1,
        (∃! a : ℝ, a ∈ Ioc (0:ℝ) 1 ∧ d * lpT f n lam a = a * oppCdf f n a) ∧
        ∀ a ∈ Ioc (0:ℝ) 1, d * lpT f n lam a = a * oppCdf f n a →
          (∃ σs : Kernel ℝ ℝ, IsBNE (lpMech n d lam) f (fun _ => σs)) ∧
          ∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (lpMech n d lam) f σ →
            expRevenue (lpMech n d lam) f σ = revCurve f n a ∧
            ∀ i, interimQ (lpMech n d lam) f σ i =ᵐ[typeMeasure f]
                (fun v => if a ≤ v then oppCdf f n v else 0) ∧
              interimM (lpMech n d lam) f σ i =ᵐ[typeMeasure f]
                (fun v => if a ≤ v then lpM f n a v else 0) ∧
              ∀ b ∈ Icc (0:ℝ) 1, d ≤ b → 0 < b → bidLaw f (σ i) {b} = 0) ∧
      (∀ τ : ℝ, ∀ π : ℝ → ℝ, IsGradedReserve π → IsTauAdmissible f n τ π →
        ∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (gradedMech n π) f σ →
          τ ≤ expRevenue (gradedMech n π) f σ)) ∧
    (∀ k : ℝ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ε < 1 →
      revCurve (powerDensity k) n 0 < (1 - ε) * optRevenue (powerDensity k) n →
      (∃! p, pMin k n < p ∧ lhs3 k n p = (1 - ε) * optRevenue (powerDensity k) n) ∧
      ∀ p, pMin k n < p → lhs3 k n p = (1 - ε) * optRevenue (powerDensity k) n →
        IsTauAdmissibleAll n (powerDensity k) ((1 - ε) * optRevenue (powerDensity k) n)
          (piStar k n p) ∧
        (∀ π : ℝ → ℝ, IsGradedReserve π →
          IsTauAdmissibleAll n (powerDensity k) ((1 - ε) * optRevenue (powerDensity k) n) π →
          revAnc (powerDensity k) n π ≤ revAnc (powerDensity k) n (piStar k n p)) ∧
        revAnc (powerDensity k) n (piStar k n p) =
          powN k n / (powN k n + 1)
            * (1 - bZero k n p ^ (powN k n + 1) * (p / (p + powN k n + 1))) ∧
        (∃ hβ : Measurable (betaStar k n p),
          IsBNE (gradedMech n (piStar k n p)) (powerDensity k)
            (fun _ => Kernel.deterministic (betaStar k n p) hβ)) ∧
        (∀ v ∈ Icc (0:ℝ) 1, piStar k n p (betaStar k n p v) = sStar k n p v) ∧
        (∀ σ : Fin n → Kernel ℝ ℝ, IsBNE (gradedMech n (piStar k n p)) (powerDensity k) σ →
          ∀ i, ∀ᵐ v ∂(typeMeasure (powerDensity k)), σ i v = Measure.dirac (betaStar k n p v)) ∧
        (∀ b ∈ Ioc (0:ℝ) 1, 0 < piStar k n p b) ∧
        vbar k n p < 1 ∧ (∀ v ∈ Icc (vbar k n p) 1, sStar k n p v = 1)) := by sorry

end GradedReserve.Supplement
