-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_dualGraphCovering_of_prime_of_five_le
-- name    : ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/17820233-91ac-5c6c-bde2-90604923c395
-- title:
--   Uniform semistable covering of X₀(N) at every prime
-- statement:
--   Let $N$ be a nonzero natural number which is prime with $5 \le N$, let $s : \mathrm{Fin}\,r \to \overline{\mathcal F}_N$ be a family in the geometric modular function field $\overline{\mathcal F}_N =$ `modularFunctionFieldBar N` which is an embedding basis, i.e. $\overline{\mathbb Q}$-linearly independent with span the Riemann–Roch space of `embDivisor N`, and let $p$ be a prime. Then there are a profile: natural numbers $n, m, B, k$ and a real $Cc$, such that for every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ there exist fields $\overline F_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, component charts $C_i$ of $\overline{\mathcal F}_N$ with values in $\overline F_i$, two families of annuli $An_e, An'_e$ ($e \in \mathrm{Fin}\,m$), maps $\mathrm{src},\mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, places $xs_e$ of $\overline F_{\mathrm{src}(e)}$ and $xt_e$ of $\overline F_{\mathrm{tgt}(e)}$, and functions $T_i$ assigning an element of $\overline{\mathcal F}_N$ to each place of $\overline F_i$, such that: for each $e$, $An'_e$ has the same domain and the same modulus as $An_e$, that modulus is nonzero in $\overline{\mathbb Q}$, and the product of the two parameters is the image of the modulus; $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $xs_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $xt_e$; every node of every chart is an end $\langle \mathrm{src}(e), xs_e\rangle$ or $\langle \mathrm{tgt}(e), xt_e\rangle$ of some edge, and exactly one element of $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$ gives that end; every place of $\overline{\mathcal F}_N$ over $\overline{\mathbb Q}$ lies in the domain of exactly one chart and of no annulus, or of exactly one annulus and of no chart; some chart contains the cusp `cuspInftyBar N` and on it each $s_l$ has, after scaling by some $c \ne 0$ with $p^B c$ and $p^B c^{-1}$ in $A$, nonzero residue; each $\overline F_i$ has principal divisors and all its places are rational; the graph on $\mathrm{Fin}\,n$ whose edges join $\mathrm{src}(e)$ to $\mathrm{tgt}(e)$ is connected (any two vertices are related by the reflexive–transitive closure); each modulus divides $p^k$ in $A$; for each chart $i$ and each $P$ in its domain, $T_i(\mathrm{placeMap}\,P)$ minus the constant $P(T_i(\mathrm{placeMap}\,P))$ lies in the chart's valuation ring, has nonzero residue of order $1$ at $\mathrm{placeMap}\,P$, has positive order at $P$ and order $0$ at every other place $Q$ of the chart with the same reduction; and, for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose unit ball is exactly $A$, three comparison bounds with constant $Cc$ between the chordal proximity `prox` of the normalised coordinate vectors `evalVec s` at two distinct places and local data: on an annulus, $|\mathrm{prox} + \log \mu(P(\mathrm{param}) - Q(\mathrm{param}))| \le Cc\,(-\log \mu(\text{modulus}))$; on a chart, $|\mathrm{prox} + \log \mu(P(T_i) - Q(T_i))| \le Cc\,(-\log \mu(p))$ when $P$ and $Q$ have the same reduction and $|\mathrm{prox}| \le Cc\,(-\log\mu(p))$ when they do not (both under the assumption that the coordinate vectors are not proportional); and $|\mathrm{prox}| \le Cc\,(-\log\mu(p))$ for any two places not sharing a chart or an annulus.
--
--   This packages the semistable reduction of $X_0(N)$ at an arbitrary prime $p$, for prime level $N \ge 5$, as a covering of the places of the geometric function field by finitely many component charts and annuli whose incidence is the dual graph of the reduction, together with bounds comparing chordal proximity of points to the local coordinates on charts and annuli, all with a profile and a constant independent of the chosen valuation ring above $p$. It is used in the construction of the regularized ultrametric Green kernel on $X_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_dualGraphCovering_of_prime_of_five_le.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime) :
    ∃ (n m B k : ℕ) (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∃ (Fbar : Fin n → Type) (_ : ∀ i, Field (Fbar i))
      (_ : ∀ i, Algebra (IsLocalRing.ResidueField ↥A) (Fbar i))
      (C : ∀ i, ComponentChart A (modularFunctionFieldBar N) (Fbar i))
      (An An' : Fin m → Annulus A (modularFunctionFieldBar N)) (src tgt : Fin m → Fin n)
      (xs : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (src e)))
      (xt : ∀ e, Place (IsLocalRing.ResidueField ↥A) (Fbar (tgt e)))
      (T : ∀ i, Place (IsLocalRing.ResidueField ↥A) (Fbar i) → modularFunctionFieldBar N),
      (∀ e, (An' e).dom = (An e).dom ∧ (An' e).modulus = (An e).modulus ∧
        ((An e).modulus : AlgebraicClosure ℚ) ≠ 0 ∧
        (An' e).param * (An e).param
          = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An e).modulus : AlgebraicClosure ℚ)) ∧
      (∀ e, (An e).IsAttached (C (src e)) (xs e) ∧ (An' e).IsAttached (C (tgt e)) (xt e)) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∃ e,
        (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩ ∨
        (⟨tgt e, xt e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (C i).nodes, ∀ E E' : Fin m ⊕ Fin m,
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨src e, xs e⟩ : Σ j, Place (IsLocalRing.ResidueField ↥A) (Fbar j)))
            (fun e => ⟨tgt e, xt e⟩) E' = ⟨i, x⟩ → E = E') ∧
      (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        (∃ i, P ∈ (C i).dom ∧ (∀ j, P ∈ (C j).dom → j = i) ∧ ∀ e, P ∉ (An e).dom) ∨
        (∃ e, P ∈ (An e).dom ∧ (∀ e', P ∈ (An e').dom → e' = e) ∧ ∀ i, P ∉ (C i).dom)) ∧
      (∃ i, cuspInftyBar N ∈ (C i).dom ∧
        ∀ l : Fin r, ∃ c : AlgebraicClosure ℚ, c ≠ 0 ∧ (p : AlgebraicClosure ℚ) ^ B * c ∈ A ∧
          (p : AlgebraicClosure ℚ) ^ B * c⁻¹ ∈ A ∧
          ∃ h : c • s l ∈ (C i).integers, (C i).residue ⟨c • s l, h⟩ ≠ 0) ∧
      (∀ i, HasPrincipalDivisors (IsLocalRing.ResidueField ↥A) (Fbar i) ∧
        ∀ x : Place (IsLocalRing.ResidueField ↥A) (Fbar i), x.IsRational) ∧
      (∀ i j : Fin n, Relation.ReflTransGen
        (fun a b : Fin n => ∃ e, (src e = a ∧ tgt e = b) ∨ (src e = b ∧ tgt e = a)) i j) ∧
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        (p : AlgebraicClosure ℚ) ^ k = ((An e).modulus : AlgebraicClosure ℚ) * a) ∧
      (∀ i, ∀ P ∈ (C i).dom,
        ∃ h : T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))
              ∈ (C i).integers,
          (C i).residue ⟨_, h⟩ ≠ 0 ∧ ((C i).placeMap P).ord ((C i).residue ⟨_, h⟩) = 1 ∧
          0 < P.ord (T i ((C i).placeMap P)
            - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) ∧
          ∀ Q ∈ (C i).dom, (C i).placeMap Q = (C i).placeMap P → Q ≠ P →
            Q.ord (T i ((C i).placeMap P)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (P.evalAt (T i ((C i).placeMap P)))) = 0) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ e, ∀ P ∈ (An e).dom, ∀ Q ∈ (An e).dom, P ≠ Q →
          (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
          |prox μ (evalVec s P) (evalVec s Q)
              + Real.log (μ (P.evalAt (An e).param - Q.evalAt (An e).param))|
            ≤ Cc * (-Real.log (μ ((An e).modulus : AlgebraicClosure ℚ)))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ i, ∀ P ∈ (C i).dom, ∀ Q ∈ (C i).dom, P ≠ Q →
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          ((C i).placeMap P = (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)
                + Real.log (μ (P.evalAt (T i ((C i).placeMap P)) - Q.evalAt (T i ((C i).placeMap P))))|
              ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
          ((C i).placeMap P ≠ (C i).placeMap Q →
            |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ))))) ∧
      (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
        (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
        ∀ P Q : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          (∀ i, P ∈ (C i).dom → Q ∉ (C i).dom) → (∀ e, P ∈ (An e).dom → Q ∉ (An e).dom) →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) := by sorry
