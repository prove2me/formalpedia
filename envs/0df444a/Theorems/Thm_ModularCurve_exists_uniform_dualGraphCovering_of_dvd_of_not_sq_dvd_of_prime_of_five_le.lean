-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le
-- name    : ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/cfb68429-d1ee-59e4-9eba-a3791aa3929e
-- title:
--   Uniform dual-graph covering at a prime dividing prime level
-- statement:
--   Let $N$ be a prime with $5 \le N$, let $s : \mathrm{Fin}\,r \to \overline{F}_N$ be a family in the geometric modular function field `modularFunctionFieldBar N` which is `IsEmbBasis N`, i.e. linearly independent over $\overline{\mathbb{Q}}$ and spanning the Riemann–Roch space of `embDivisor N`, and let $p$ be a prime with $p \mid N$ and $p^2 \nmid N$. Then there are natural numbers $n, m, B, k$ and a real $Cc$, independent of the valuation ring, such that for every valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ there exist fields $\overline{F}_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, component charts $C_i$ of $\overline{F}_N$ over $A$ with values in $\overline{F}_i$, annuli $An_e, An'_e$ ($e \in \mathrm{Fin}\,m$) in $\overline{F}_N$ over $A$, maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, places $xs_e$ of $\overline{F}_{\mathrm{src}(e)}$ and $xt_e$ of $\overline{F}_{\mathrm{tgt}(e)}$ over the residue field of $A$, and functions $T_i$ assigning to each place of $\overline{F}_i$ an element of $\overline{F}_N$, subject to the following. (i) For each $e$, $An'_e$ has the same domain and the same (nonzero) modulus as $An_e$, and the product of the two parameters is the image of that modulus; (ii) $An_e$ is attached to $C_{\mathrm{src}(e)}$ at $xs_e$ and $An'_e$ to $C_{\mathrm{tgt}(e)}$ at $xt_e$ in the sense of `IsAttached`; (iii) every node of every chart is an end $(\mathrm{src}(e), xs_e)$ or $(\mathrm{tgt}(e), xt_e)$ of some edge, and (iv) each node is such an end for exactly one element of $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$; (v) every place of $\overline{F}_N$ over $\overline{\mathbb{Q}}$ lies either in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; (vi) the cusp `cuspInftyBar N` lies in some chart $C_i$, and for every $l$ there is $c \neq 0$ with $p^B c$ and $p^B c^{-1}$ in $A$ such that $c \cdot s_l$ lies in the integers of $C_i$ with nonzero residue; (vii) each $\overline{F}_i$ has principal divisors of degree zero and all its places are rational; (viii) the graph on $\mathrm{Fin}\,n$ with edges given by $\mathrm{src}, \mathrm{tgt}$ is connected; (ix) each annulus modulus divides $p^k$ in $A$; (x) for each chart $C_i$ and each $P$ in its domain, the function $T_i(\mathrm{placeMap}\,P)$ minus the constant $P(\!T_i(\mathrm{placeMap}\,P)\!)$ lies in the integers of $C_i$, has nonzero residue of order $1$ at $\mathrm{placeMap}\,P$, has positive order at $P$, and order $0$ at every other place of the domain with the same image under $\mathrm{placeMap}$; and (xi) three proximity estimates: for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose closed unit ball is exactly $A$, and for places $P \neq Q$ whose coordinate vectors $\mathrm{evalVec}\,s$ are not proportional, $|\mathrm{prox}_\mu + \log \mu(P(\mathrm{param}) - Q(\mathrm{param}))| \le Cc\,(-\log \mu(\mathrm{modulus}))$ when $P, Q$ lie in one annulus $An_e$; $|\mathrm{prox}_\mu + \log \mu(P(T_i) - Q(T_i))| \le Cc\,(-\log \mu(p))$ when $P, Q$ lie in one chart with the same image under $\mathrm{placeMap}$, and $|\mathrm{prox}_\mu| \le Cc\,(-\log \mu(p))$ when their images differ; and $|\mathrm{prox}_\mu| \le Cc\,(-\log \mu(p))$ for any $P, Q$ sharing no chart domain and no annulus domain. Here $\mathrm{prox}_\mu(x,y) = \log \sup_i \mu(x_i) + \log \sup_i \mu(y_i) - \log \sup_{i,j} \mu(x_i y_j - x_j y_i)$.
--
--   This is the multiplicative-reduction case of the uniform semistable covering of the modular curve of prime level $N \ge 5$: a valuation-theoretic rendering of the Deligne–Rapoport model at a prime exactly dividing the level, in which the reduction is read off the function field as finitely many component charts glued along annuli whose combinatorics form the dual graph, each node carrying exactly one annulus end, together with comparison estimates between the chordal proximity of the projective embedding by $s$ and the covering. It is the case $p \mid N$ of [`ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le), which assembles it with the remaining primes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
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
