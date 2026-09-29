-- Prove2me | Theorems.Thm_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le
-- name    : ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/a5a6ebe2-dfa6-539e-9893-898e1ca7ca43
-- title:
--   Uniform certified multiplicative covering of the level-N modular curve
-- statement:
--   Throughout, $\bar{\mathbb Q}$ denotes `AlgebraicClosure ℚ` and $F =$ `modularFunctionFieldBar N` is the subfield of the Laurent series field $\bar{\mathbb Q}((q))$ generated over $\bar{\mathbb Q}$ by the coefficientwise images of the elements of the full level-$N$ modular function field `modularFunctionFieldFull N` over $\mathbb Q$. "Place" is used in the sense of the project's structure `Place K F`: a valuation subring of $F$ containing the image of $K$, different from $F$, and a principal ideal ring; for such a place $v$, $v.\mathrm{ord}$ is the associated normalised integer valuation, $v.\mathrm{evalAt}$ is evaluation into $K$ through the residue field (zero outside the valuation subring), and $v$ is rational when $K$ surjects onto its residue field.
--
--   The inputs are: a prime $N \ge 5$; a natural number $r$ and a family $s : \mathrm{Fin}\ r \to F$ satisfying `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\bar{\mathbb Q}$ and its $\bar{\mathbb Q}$-span is the Riemann–Roch space `riemannRochSpace (embDivisor N)` of the divisor `embDegree N` times the $q$-adic cusp `cuspInftyBar N`; and a prime $p$ with $p \mid N$ and $p^2 \nmid N$.
--
--   The assertion is the existence of natural numbers $n$, $m$, $B$, $k$, a real number $C_c$, a family $t : \mathrm{Fin}\ r \to F$, two $r \times r$ matrices $M$, $M^{-1}$ (written `Minv`) over $\bar{\mathbb Q}$, a function $\mathrm{nexp} : \mathrm{Fin}\ r \to \mathbb N$ and a natural number $B_\ell$, subject to the following uniform conditions: $0 < m$; $t_l = 1$ for the index $l$ with underlying natural number $0$; $s_i = \sum_j M_{ij}\, t_j$ (the matrix entries acting through $\bar{\mathbb Q} \to F$); $M^{-1}M = MM^{-1} = 1$; $\mathrm{nexp}$ vanishes at the index $0$, is $\ge 1$ at every index $l \ge 1$, and is bounded by $k$.
--
--   Moreover, for every valuation subring $A$ of $\bar{\mathbb Q}$ with `A.LiesOverPrime p`, that is with $p$ a nonunit of $A$, there exist: fields $\bar F(i)$ for $i \in \mathrm{Fin}\ n$, each an algebra over the residue field $\kappa = \mathrm{ResidueField}\ A$; component charts $C(i) :$ `ComponentChart A F (Fbar i)` (each consisting of a valuation subring $C(i).\mathrm{integers}$ of $F$, a surjective residue map $C(i).\mathrm{residue}$ onto $\bar F(i)$ with kernel the maximal ideal, a set $C(i).\mathrm{dom}$ of places of $F$ over $\bar{\mathbb Q}$, a finite set $C(i).\mathrm{nodes}$ of places of $\bar F(i)$ over $\kappa$, and a specialisation map $C(i).\mathrm{placeMap}$, together with the compatibility axioms of that structure); two families of annuli $\mathrm{An}, \mathrm{An}' : \mathrm{Fin}\ m \to$ `Annulus A F` (each with a domain of places, a parameter in $F$, and a modulus in the maximal ideal of $A$, subject to the axioms of that structure); endpoint maps $\mathrm{src}, \mathrm{tgt} : \mathrm{Fin}\ m \to \mathrm{Fin}\ n$; nodes $x_s(e)$ on $\bar F(\mathrm{src}\ e)$ and $x_t(e)$ on $\bar F(\mathrm{tgt}\ e)$; and fibre coordinates $T(i)$ assigning to each place of $\bar F(i)$ over $\kappa$ an element of $F$. These data satisfy the following conjuncts.
--
--   (1) Paired annuli: for each $e$, $\mathrm{An}'(e)$ and $\mathrm{An}(e)$ have the same domain and the same modulus, that modulus is nonzero in $\bar{\mathbb Q}$, and the product of the two parameters equals the image of the modulus in $F$.
--
--   (2) Attachment: for each $e$, $\mathrm{An}(e)$ is attached to $C(\mathrm{src}\ e)$ at $x_s(e)$ and $\mathrm{An}'(e)$ is attached to $C(\mathrm{tgt}\ e)$ at $x_t(e)$, in the sense of `Annulus.IsAttached`: the node lies in the chart's node set, the annulus parameter is integral on the chart with residue of order exactly $1$ at the node, and for every chart-integral $f$ with nonzero residue and with order $0$ at all places of the annulus, the quantity $P.\mathrm{evalAt}(f)\cdot P.\mathrm{evalAt}(\mathrm{param})^{-\mathrm{ord}_{x}(\mathrm{residue}\ f)}$ is a unit of $A$ at every place $P$ of the annulus.
--
--   (3) Every node is an endpoint: for each $i$ and each $x \in C(i).\mathrm{nodes}$ there is an $e$ with $(\mathrm{src}\ e, x_s(e)) = (i,x)$ or $(\mathrm{tgt}\ e, x_t(e)) = (i,x)$, as pairs in the sigma type of nodes.
--
--   (4) Each node is an endpoint only once: for each $i$ and $x \in C(i).\mathrm{nodes}$, the map from $\mathrm{Fin}\ m \oplus \mathrm{Fin}\ m$ sending a left $e$ to $(\mathrm{src}\ e, x_s(e))$ and a right $e$ to $(\mathrm{tgt}\ e, x_t(e))$ takes the value $(i,x)$ at most once.
--
--   (5) Partition of places: every place $P$ of $F$ over $\bar{\mathbb Q}$ either lies in exactly one chart domain and in no annulus domain, or lies in exactly one annulus domain and in no chart domain.
--
--   (6) Cusp chart and bounded scaling: there is an $i$ with $\mathrm{cuspInftyBar}\ N \in C(i).\mathrm{dom}$ such that for every $l$ there is $c \ne 0$ in $\bar{\mathbb Q}$ with $p^B c \in A$ and $p^B c^{-1} \in A$, with $c \cdot s_l$ integral on that chart and with nonzero residue.
--
--   (7) Reduction components: for each $i$, the extension $\kappa \to \bar F(i)$ has principal divisors (every nonzero element of $\bar F(i)$ has a divisor of degree zero recording its orders at all places) and every place of $\bar F(i)$ over $\kappa$ is rational.
--
--   (8) Connectedness: any two $i, j \in \mathrm{Fin}\ n$ are joined by a chain, in the reflexive–transitive closure of the relation "there is an $e$ with $\mathrm{src}\ e = a$, $\mathrm{tgt}\ e = b$ or with $\mathrm{src}\ e = b$, $\mathrm{tgt}\ e = a$".
--
--   (9) Moduli: for each $e$ the modulus of $\mathrm{An}(e)$ divides $p^k$ in $A$, and $p$ divides that modulus in $A$.
--
--   (10) Fibre coordinates: for each $i$ and each $P \in C(i).\mathrm{dom}$, setting $u = T(i)(C(i).\mathrm{placeMap}\ P)$, the element $u - P.\mathrm{evalAt}(u)$ is integral on $C(i)$, its residue is nonzero, that residue has order $1$ at $C(i).\mathrm{placeMap}\ P$, $P.\mathrm{ord}(u - P.\mathrm{evalAt}(u)) > 0$, and $Q.\mathrm{ord}(u - P.\mathrm{evalAt}(u)) = 0$ for every $Q \in C(i).\mathrm{dom}$ with the same image under $C(i).\mathrm{placeMap}$ and $Q \ne P$.
--
--   (11) In-chart proximity comparison: for every nonarchimedean absolute value $\mu$ on $\bar{\mathbb Q}$ whose unit ball is exactly $A$, for every $i$ and all $P \ne Q$ in $C(i).\mathrm{dom}$ admitting indices $i', j'$ with $\mathrm{evalVec}(s,P)_{i'}\,\mathrm{evalVec}(s,Q)_{j'} \ne \mathrm{evalVec}(s,P)_{j'}\,\mathrm{evalVec}(s,Q)_{i'}$, where $\mathrm{evalVec}(s,v)_i = v.\mathrm{evalAt}(s_i\, s_{\mathrm{pivot}}^{-1})$ and $\mathrm{prox}\ \mu\ x\ y = \log \sup_i \mu(x_i) + \log \sup_j \mu(y_j) - \log \sup_{(i,j)} \mu(x_i y_j - x_j y_i)$: if $P$ and $Q$ specialise to the same place then $|\mathrm{prox}\ \mu\ \mathrm{evalVec}(s,P)\ \mathrm{evalVec}(s,Q) + \log \mu(P.\mathrm{evalAt}(u) - Q.\mathrm{evalAt}(u))| \le C_c\,(-\log \mu(p))$ with $u$ the fibre coordinate at $C(i).\mathrm{placeMap}\ P$; and if they specialise to distinct places then $|\mathrm{prox}\ \mu\ \mathrm{evalVec}(s,P)\ \mathrm{evalVec}(s,Q)| \le C_c\,(-\log \mu(p))$.
--
--   (12) Cross comparison: for $\mu$ as in (11) and all places $P, Q$ of $F$ such that no chart domain contains both and no annulus domain contains both, and which satisfy the same nondegeneracy condition on $\mathrm{evalVec}$, one has $|\mathrm{prox}\ \mu\ \mathrm{evalVec}(s,P)\ \mathrm{evalVec}(s,Q)| \le C_c\,(-\log \mu(p))$.
--
--   (13) Link budget: $p^{B_\ell} M_{ij} \in A$ and $p^{B_\ell} (M^{-1})_{ij} \in A$ for all $i,j$.
--
--   (14) Far end of $t$: for each $e$ and each $l$, $t_l$ is integral on $C(\mathrm{tgt}\ e)$ with nonzero residue, and for $l \ge 1$ that residue has order $\ge 1$ at $x_t(e)$.
--
--   (15) Far-end pivot: for each $e$ there is an $l \ge 1$ with $t_l$ integral on $C(\mathrm{tgt}\ e)$ and residue of order exactly $1$ at $x_t(e)$.
--
--   (16) Near end of $t$: for each $e$ and each $l$, $(p^{\mathrm{nexp}\ l})^{-1} t_l$ is integral on $C(\mathrm{src}\ e)$ with nonzero residue.
--
--   (17) Smallness on the tube: for each $e$, each place $R \in \mathrm{An}(e).\mathrm{dom}$ and each $l \ge 1$, $t_l$ lies in the valuation subring of $R$ and $R.\mathrm{evalAt}(t_l)$ lies in $A$ and in its maximal ideal.
--
--   (18) Width and certified delivered family: for each $e$ there is $w \ge 1$ together with a unit $u$ of $A$ (i.e. $u, u^{-1} \in A$) such that the modulus of $\mathrm{An}(e)$ equals $p^w u$; and if $2 \le w$ there are matrices $U$, $U^{-1}$ (written `Uinv`) over $\bar{\mathbb Q}$ and a family $f : \mathrm{Fin}\ r \to F$ with: all entries of $U$ and $U^{-1}$ in $A$; $U^{-1}U = UU^{-1} = 1$; $f_l = \sum_j U_{lj} t_j$; each $(p^{\mathrm{nexp}\ l})^{-1} f_l$ integral on $C(\mathrm{src}\ e)$ with nonzero residue, with residue of order $-\lfloor \mathrm{nexp}\ l / w\rfloor$ at $x_s(e)$ (natural-number division, cast to $\mathbb Z$), and with these residues linearly independent over $\kappa$; each $f_l$ integral on $C(\mathrm{tgt}\ e)$ with nonzero residue, of order $\ge 1$ at $x_t(e)$ when $l \ge 1$; some $l \ge 1$ for which that order is exactly $1$; $f_l = 1$ at the index $0$; for every $R \in \mathrm{An}(e).\mathrm{dom}$ and every $l \ge 1$, $f_l$ in the valuation subring of $R$ with $R.\mathrm{evalAt}(f_l)$ in the maximal ideal of $A$; and finally one of the two certificates: either there is $l \ge 1$ whose far-end residue has order exactly $1$ at $x_t(e)$ and with $\mathrm{nexp}\ l = w$, or there are indices $m_1, m_2 \ge 1$ whose far-end residues both have order exactly $1$ at $x_t(e)$, with $\mathrm{nexp}\ m_1 < \mathrm{nexp}\ m_2 < w$ and $\mathrm{nexp}\ m_1 + w \le 2\,\mathrm{nexp}\ m_2$, and an element $c \in \kappa$ such that the near-chart residue of $(p^{\mathrm{nexp}\ m_1})^{-1} f_{m_1}$ minus the image of $c$ has order exactly $1$ at $x_s(e)$.
--
--   (19) Supersingular annuli: for every $a \in \kappa$ lying in `ssJSet p κ` (every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $a$ has no nonzero affine point killed by $p$) with $a \ne 0$ and $a \ne 1728$, there is an $e$ such that the parameter of $\mathrm{An}(e)$ equals $j(q^p) - j^p$, where $j$ denotes the element of $F$ given by the coefficient-embedded $q$-expansion `jq` and $j(q^p)$ the element given by `qExpand ℚ p jq`; there is $x_l \in A$ with residue $a$ such that $j - x_l$ is integral on $C(\mathrm{src}\ e)$ with residue of positive order at $x_s(e)$; there is $y_l \in A$ with residue $a^p$ such that $j(q^p) - y_l$ is integral on $C(\mathrm{tgt}\ e)$ with residue of positive order at $x_t(e)$; and the modulus of $\mathrm{An}(e)$ equals $p u$ for some unit $u$ of $A$ (with $u, u^{-1} \in A$).
--
--   This packages the semistable multiplicative covering of the level-$N$ modular curve above a prime $p$ exactly dividing $N$: a dual graph of component charts joined by annuli, uniform in the valuation subring $A$ of $\bar{\mathbb Q}$ over $p$, carrying fibre coordinates, chordal proximity estimates for the embedding basis $s$, the behaviour of a normalised family $t$ at both ends of each annulus and on its tube, a delivered family with attained orders and a pivot certificate on each wide annulus, and the location of the supersingular annuli through $j$ and $j(q^p)$. It is the geometric input to [`ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le.lean

import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le (N : ℕ) [NeZero N] (hN : N.Prime) (hN5 : 5 ≤ N) {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∃ (n m B k : ℕ) (Cc : ℝ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ), 0 < m ∧
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) ∧
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) ∧
    Minv * M = 1 ∧ M * Minv = 1 ∧
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) ∧ (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) ∧ (∀ l, nexp l ≤ k) ∧
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ [DecidableEq (IsLocalRing.ResidueField ↥A)],
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
      (∀ e, ∃ a : AlgebraicClosure ℚ, a ∈ A ∧
        ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * a) ∧
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
          (∃ i' j', evalVec s P i' * evalVec s Q j' ≠ evalVec s P j' * evalVec s Q i') →
          |prox μ (evalVec s P) (evalVec s Q)| ≤ Cc * (-Real.log (μ (p : AlgebraicClosure ℚ)))) ∧
      (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) ∧
      (∀ e, ∀ l : Fin r, ∃ h : t l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨t l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩))) ∧
      (∀ e, ∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : t l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨t l, h⟩) = 1) ∧
      (∀ e, ∀ l : Fin r, ∃ h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * t l
          ∈ (C (src e)).integers, (C (src e)).residue ⟨_, h⟩ ≠ 0) ∧
      (∀ e, ∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        t l ∈ R.toValuationSubring ∧ ∃ h : R.evalAt (t l) ∈ A, (⟨R.evalAt (t l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
      (∀ e, ∃ w : ℕ, 1 ≤ w ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          (((An e).modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) ∧
        (2 ≤ w →
          ∃ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar N),
            (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) ∧ (Uinv * U = 1 ∧ U * Uinv = 1) ∧
            (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (U l j) * t j) ∧
        (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ (C (src e)).integers,
        (∀ l : Fin r, (C (src e)).residue ⟨_, hint l⟩ ≠ 0) ∧
        (∀ l : Fin r, (xs e).ord ((C (src e)).residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
        LinearIndependent (IsLocalRing.ResidueField ↥A) (fun l => (C (src e)).residue ⟨_, hint l⟩)) ∧
        (∀ l : Fin r, ∃ h : f l ∈ (C (tgt e)).integers,
        (C (tgt e)).residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩))) ∧
        (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧
        (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) ∧
        (∀ R ∈ (An e).dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
        f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) ∧
        ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
        (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ (C (tgt e)).integers, (xt e).ord ((C (tgt e)).residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ (C (src e)).integers) (c : IsLocalRing.ResidueField ↥A),
        (xs e).ord ((C (src e)).residue ⟨_, h⟩ - algebraMap (IsLocalRing.ResidueField ↥A) (Fbar (src e)) c) = 1))))) ∧
      (letI : NeZero p := ⟨hp.ne_zero⟩;
       ∀ a : IsLocalRing.ResidueField ↥A, a ∈ ssJSet p (IsLocalRing.ResidueField ↥A) →
        a ≠ 0 → a ≠ 1728 → ∃ e,
        (An e).param
          = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
            - (⟨coeffEmb (AlgebraicClosure ℚ) jq,
                coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                  (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) ^ p ∧
        (∃ xl : A, IsLocalRing.residue ↥A xl = a ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (xl : AlgebraicClosure ℚ)
              ∈ (C (src e)).integers,
            0 < (xs e).ord ((C (src e)).residue ⟨_, h⟩)) ∧
        (∃ yl : A, IsLocalRing.residue ↥A yl = a ^ p ∧
          ∃ h : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N hpN)⟩ :
                modularFunctionFieldBar N)
              - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (yl : AlgebraicClosure ℚ)
              ∈ (C (tgt e)).integers,
            0 < (xt e).ord ((C (tgt e)).residue ⟨_, h⟩)) ∧
        (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
          ((An e).modulus : AlgebraicClosure ℚ) = (p : AlgebraicClosure ℚ) * u)) := by sorry
