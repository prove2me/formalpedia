-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_dualGraphCovering_of_not_dvd
-- name    : ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/3e9c2384-f463-57e2-a2f5-6a2692a985e2
-- title:
--   Uniform semistable covering at a prime not dividing the level
-- statement:
--   Fix $N \geq 1$ and a family $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` (the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $N$) which is an `IsEmbBasis`, i.e. linearly independent over $\overline{\mathbb{Q}}$ and spanning the Riemann–Roch space of `embDivisor N`; let $p$ be a prime with $p \nmid N$. Then there are natural numbers $n, m, B, k$ and a real constant $Cc$, chosen once and for all, such that for every valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ the following data exist: fields $\overline{F}_i$ ($i \in \mathrm{Fin}\,n$) over the residue field of $A$, component charts $C_i$ of `modularFunctionFieldBar N` relative to $A$ with values in $\overline{F}_i$, annuli $\mathrm{An}_e, \mathrm{An}'_e$ ($e \in \mathrm{Fin}\,m$), maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\,m \to \mathrm{Fin}\,n$, places $x^{\mathrm{s}}_e$ of $\overline{F}_{\mathrm{src}(e)}$ and $x^{\mathrm{t}}_e$ of $\overline{F}_{\mathrm{tgt}(e)}$, and for each $i$ a map $T_i$ from places of $\overline{F}_i$ to elements of the function field, subject to: each $\mathrm{An}'_e$ has the same domain and modulus as $\mathrm{An}_e$, that modulus is nonzero in $\overline{\mathbb{Q}}$, and the two parameters multiply to the modulus; $\mathrm{An}_e$ is attached to $C_{\mathrm{src}(e)}$ at $x^{\mathrm{s}}_e$ and $\mathrm{An}'_e$ to $C_{\mathrm{tgt}(e)}$ at $x^{\mathrm{t}}_e$; every node of every chart occurs as such an end, and (end-uniqueness) occurs for exactly one element of $\mathrm{Fin}\,m \oplus \mathrm{Fin}\,m$; every place of `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ lies in exactly one chart domain and in no annulus domain, or in exactly one annulus domain and in no chart domain; some chart contains the cusp `cuspInftyBar N` and, for each basis index $l$, admits a scalar $c \neq 0$ with $p^B c$ and $p^B c^{-1}$ in $A$ such that $c \cdot s_l$ lies in the chart's integers with nonzero residue; each $\overline{F}_i$ has principal divisors over the residue field of $A$ and all its places are rational; the graph on $\mathrm{Fin}\,n$ with edges given by $\mathrm{src}, \mathrm{tgt}$ (in either orientation) is connected; each modulus divides $p^k$ in $A$; for every chart $i$ and every place $P$ of its domain, with $t = T_i(\mathrm{placeMap}\,P)$, the element $t - P.\mathrm{evalAt}(t)$ lies in the chart's integers, has nonzero residue of order $1$ at $\mathrm{placeMap}\,P$, has positive order at $P$, and order $0$ at every other place of the domain with the same reduction; and three comparison clauses, valid for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb{Q}}$ whose unit ball is exactly $A$, bounding the chordal proximity `prox` of the normalised coordinate vectors $\mathrm{evalVec}\,s$ at two places $P \neq Q$ with non-proportional coordinate vectors: on an annulus, $|\mathrm{prox} + \log \mu(P.\mathrm{evalAt}\,\mathrm{param} - Q.\mathrm{evalAt}\,\mathrm{param})| \leq Cc \cdot (-\log \mu(\mathrm{modulus}))$; on a chart, the same bound with parameter $T_i(\mathrm{placeMap}\,P)$ and with $-\log \mu(p)$ on the right when $P, Q$ have the same reduction, and $|\mathrm{prox}| \leq Cc \cdot (-\log \mu(p))$ when their reductions differ; and $|\mathrm{prox}| \leq Cc \cdot (-\log \mu(p))$ whenever $P$ and $Q$ share no chart domain and no annulus domain.
--
--   This is the good-reduction case of the uniform semistable covering of the modular curve of level $N$, expressed entirely in terms of places of its function field: above a prime $p$ not dividing $N$ one may take a single component chart and no annuli, so that the dual-graph and thickness clauses hold trivially, while the Gauss-norm, disc-parameter and proximity-comparison clauses carry the arithmetic content. It is combined with the cases $p \mid N$ in [`ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_prime_of_five_le), which assembles the uniform covering for all primes at once.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_dualGraphCovering_of_not_dvd.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_uniform_dualGraphCovering_of_not_dvd (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : ¬ p ∣ N) :
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
