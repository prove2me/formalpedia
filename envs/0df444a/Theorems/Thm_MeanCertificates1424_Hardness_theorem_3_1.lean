-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_theorem_3_1
-- name    : MeanCertificates1424.Hardness.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:26.657359+00:00
-- url     : https://prove2.me/theorems/ef365bac-73ff-4fe9-a092-1a040f17d1af
-- title:
--   Theorem 3.1 — Uniform-mean certification without audits
-- statement:
--   Let $H$ be any finite simple graph with $r$ vertices and $m\ge1$ edges, and $2\le k\le r$. For every integer $R\ge1$, the concrete constructor runs in polynomial time in $r+m+R$ and produces a feasible uniform-mean instance with no audits, $L=1$, $\epsilon=0$, reports in $\{0,1,2,3\}$, and
--
--   $$N_0=r+Rm+3(Rm+k+1),\qquad b=Rm+k,\qquad 2b<N_0.$$
--
--   Its graph is three-colorable with diameter exactly two, and every feasible real field belongs to $[0,2]^{N_0}$. More generally, for every fixed rational $\rho>0$, the defined polynomial padding preserves these properties and enforces $b\le\rho N$. Writing $p$ for the padding and $B_0=Rm+3(b+1)+p$, the two endpoints are attained and satisfy
--
--   $$\ell=\frac{B_0-2k}{N},\qquad u=\frac{B_0+R\operatorname{dk}_k(H)+k}{N},\qquad u-\ell=\frac{R\operatorname{dk}_k(H)+3k}{N}.$$
--
--   For $R=3k$, the paper writes $N=O(rm+r)$; the proof yields sufficient constant $24$ for the unpadded count. With padding the size constant depends only on fixed $\rho$. For every real $\alpha\ge1$, scaling a factor-$\alpha$ width approximation by $N/(3k)$ gives a factor-$2\alpha$ approximation to $\operatorname{dk}_k(H)$. The formal approximation transfer also permits any number $p$ of extra middle-anchor vertices, as the proof does.
--
--   The theorem supplies the concrete reduction used by both hardness corollaries, including explicit extrema over all feasible real fields.
--
--   Differences from the source:
--   - encoding: finite graphs and rational binary numerical inputs, with real candidate fields → Fin n vertices, rational input data, real feasible vectors and EReal endpoint extrema; reason: finite labels and complete-lattice extrema preserve all instances in the complexity claim; every width promise is nonempty and anchored
--   - encoding: deterministic polynomial time and ETH on the number of SAT variables → finite Mathlib multi-stack machines, explicit binary adjacency-list codecs, uniform step bounds, normalized 3CNF and sublinear exponent ETH; reason: fixes an operational encoding without an optimum, real oracle, cost annotation, or correctness hypothesis on the program
--   - encoding: the construction and polynomial padding in the proof of Theorem 3.1 → the explicit indexed gadget and p=max(0,ceil(b/rho)-N0) middle-anchor padding; reason: chooses a concrete permitted labeling and padding amount; the output properties are conclusions
--   - encoding: N=O(rm+r) for R=3k → N0≤24(rm+r), and a uniform size constant for every fixed rational rho>0; reason: the displayed count with k≤r and m≥1 yields the sufficient constant 24; padding adds at most ceil(b/rho) vertices; no numerical runtime exponent is invented
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 3.1, printed p.7 (PDF p.9); proof and explicit extrema, printed pp.7–8 (PDF pp.9–10)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Computation

set_option autoImplicit false

namespace MeanCertificates1424.Hardness

/-- Theorem 3.1, printed p.7 / PDF p.9; exact extremizers from its proof on
printed pp.7–8 / PDF pp.9–10. The proof's size count yields the sufficient
constant 24 for unpadded R=3k; padded size constants depend only on fixed ρ.
All numerical outputs and every field range are conclusions, not hypotheses. -/
theorem theorem_3_1 :
    Constructs (fun {_} _ _ _ => 0) ∧
    (∀ ρ : ℚ, 0 < ρ → Constructs (fun {_} H k R => padding H k R ρ)) ∧
    (∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k R : ℕ),
      Admissible H k → 1 ≤ R →
      GadgetGuarantees H k R 0 ∧
      (gadget H k R 0).n = r + R * edgeCount H + 3 * (R * edgeCount H + k + 1) ∧
      (gadget H k R 0).budget = R * edgeCount H + k ∧
      (∀ ρ : ℚ, 0 < ρ →
        let p := padding H k R ρ
        GadgetGuarantees H k R p ∧
        ((gadget H k R p).budget : ℚ) ≤ ρ * (gadget H k R p).n)) ∧
    (∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k : ℕ), Admissible H k →
      (gadget H k (3 * k) 0).n ≤ 24 * (r * edgeCount H + r) ∧
      ∀ (p : ℕ) (α a : ℝ), 1 ≤ α →
        WidthApprox α (gadget H k (3 * k) p) a →
        (dks H k : ℝ) / (2 * α) ≤ (gadgetSize H k (3 * k) p : ℝ) / (3 * k) * a ∧
        (gadgetSize H k (3 * k) p : ℝ) / (3 * k) * a ≤ (2 * α) * dks H k) ∧
    (∀ ρ : ℚ, 0 < ρ → ∃ C : ℕ, 0 < C ∧
      ∀ (r : ℕ) (H : SimpleGraph (Fin r)) (k : ℕ), Admissible H k →
        (gadget H k (3 * k) (padding H k (3 * k) ρ)).n ≤ C * (r * edgeCount H + r)) := by sorry

end MeanCertificates1424.Hardness
