-- Prove2me | Theorems.Thm_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily
-- name    : ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/fd0d4f58-97cb-5d08-aa71-8b963bf401d3
-- title:
--   Annulus proximity comparison at a wide node above p ∥ N
-- statement:
--   Fix $N \ge 1$ and a family $s : \mathrm{Fin}\,r \to$ `modularFunctionFieldBar N` which is an embedding basis, i.e. linearly independent over $\overline{\mathbb Q}$ and spanning the Riemann–Roch space of `embDivisor N`; fix a prime $p$ with $p \mid N$ and $p^2 \nmid N$. The assertion is that for every $k_0$, every family $t$ with $t_0 = 1$, every pair of mutually inverse matrices $M, M^{-1}$ over $\overline{\mathbb Q}$ with $s_i = \sum_j M_{ij} t_j$, every exponent vector $n$ with $n_0 = 0$, $n_l \ge 1$ for $l \ge 1$ and $n_l \le k_0$, and every $B$, there is a real constant $C$ such that the following holds for every valuation subring $A \subseteq \overline{\mathbb Q}$ in which $p$ is a nonunit. Let $C$-charts $\mathcal C$, $\mathcal C'$ be component charts of `modularFunctionFieldBar N` over $A$ with values in fields $\bar F$, $\bar F'$ over the residue field of $A$, let $x$, $x'$ be places of $\bar F$, $\bar F'$ over that residue field, and let $An$, $An'$ be annuli attached to $(\mathcal C,x)$ and $(\mathcal C',x')$ respectively, sharing the same domain and the same modulus $\pi \ne 0$, with $An'.\mathrm{param} \cdot An.\mathrm{param} = \pi$. Let $\pi_x \ne 0$ lie in the maximal ideal of $A$, with $\pi = u^{-1}\pi_x$ for a unit $u$ of $A$, with $p^{k_0} \in \pi_x A$ and $\pi_x \in pA$. Let $U, U^{-1}$ be mutually inverse matrices with all entries in $A$ and $f_l = \sum_j U_{lj} t_j$, and let $w \ge 2$ satisfy $\pi = p^w \cdot (\text{unit of } A)$. Assume: each $p^{-n_l} f_l$ lies in $\mathcal C$'s integers with nonzero residue, $\operatorname{ord}_x$ of that residue equal to $-\lfloor n_l/w \rfloor$, and these residues linearly independent over the residue field of $A$; all entries of $p^B M$ and $p^B M^{-1}$ lie in $A$; each $f_l$ lies in $\mathcal C'$'s integers with nonzero residue, of $\operatorname{ord}_{x'} \ge 1$ when $l \ge 1$, with $\operatorname{ord}_{x'} = 1$ for at least one such $l$; $f_0 = 1$; for every place $R$ in $An.\mathrm{dom}$ and every $l \ge 1$, $f_l$ is $R$-integral with $R$-value in the maximal ideal of $A$; and a certificate holds, namely either some $l \ge 1$ has $\operatorname{ord}_{x'}$ of its $\mathcal C'$-residue equal to $1$ and $n_l = w$, or there are $m_1, m_2 \ge 1$, both with $\mathcal C'$-residue of $\operatorname{ord}_{x'}$ equal to $1$, with $n_{m_1} < n_{m_2} < w$ and $n_{m_1} + w \le 2 n_{m_2}$, such that $p^{-n_{m_1}} f_{m_1}$ is $\mathcal C$-integral and its residue differs from some element of the residue field of $A$ by an element of $\operatorname{ord}_x$ exactly $1$. Then for every nonarchimedean absolute value $\mu$ on $\overline{\mathbb Q}$ whose closed unit ball is exactly $A$, and all distinct places $P, Q$ in $An.\mathrm{dom}$ whose coordinate vectors $\mathrm{evalVec}\,s\,P$, $\mathrm{evalVec}\,s\,Q$ admit a nonvanishing $2 \times 2$ minor,
--   $$\bigl|\,\mathrm{prox}_\mu(\mathrm{evalVec}\,s\,P, \mathrm{evalVec}\,s\,Q) + \log \mu\bigl(P(An.\mathrm{param}) - Q(An.\mathrm{param})\bigr)\bigr| \le C \cdot \bigl(-\log \mu(\pi)\bigr),$$
--   where $\mathrm{prox}_\mu(y,z) = \log \sup_i \mu(y_i) + \log \sup_i \mu(z_i) - \log \sup_{i,j} \mu(y_i z_j - y_j z_i)$, $P(\cdot)$ denotes the residue-field evaluation `Place.evalAt`, and $\mathrm{evalVec}\,s\,P$ is the vector of values $P(s_i/s_{\text{pivot}})$.
--
--   This is the comparison, uniform in the valuation subring above $p$ and in the annulus, between the chordal proximity of two points of an annulus in the projective coordinates given by an embedding basis of level $N$ and the distance of their parameter values; it treats a node of width $w \ge 2$, where the certificate on the exponents $n_l$ replaces the width-one hypothesis. It feeds the uniform dual-graph covering statement [`ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_dualGraphCovering_of_dvd_of_not_sq_dvd_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_annulusComparison_of_attached_at_both_ends_of_certifiedFamily.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_AlgebraicCurve_ChordalProximity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve IsLocalRing

theorem ModularCurve.annulusComparison_of_attached_at_both_ends_of_certifiedFamily (N : ℕ) [NeZero N]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) (p : ℕ) (hp : p.Prime)
    (hpN : p ∣ N) (hp2 : ¬ p ^ 2 ∣ N) :
    ∀ (k₀ : ℕ) (t : Fin r → modularFunctionFieldBar N)
      (M Minv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (nexp : Fin r → ℕ) (Bl : ℕ),
    (∀ l : Fin r, (l : ℕ) = 0 → t l = 1) →
    (∀ i, s i = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (M i j) * t j) →
    Minv * M = 1 → M * Minv = 1 →
    (∀ l : Fin r, (l : ℕ) = 0 → nexp l = 0) → (∀ l : Fin r, 1 ≤ (l : ℕ) → 1 ≤ nexp l) →
    (∀ l, nexp l ≤ k₀) →
    ∃ (Cc : ℝ), ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime p →
    ∀ {Fbar Fbar' : Type} [Field Fbar] [Algebra (ResidueField ↥A) Fbar]
      [Field Fbar'] [Algebra (ResidueField ↥A) Fbar']
      (C : ComponentChart A (modularFunctionFieldBar N) Fbar)
      (C' : ComponentChart A (modularFunctionFieldBar N) Fbar')
      (x : Place (ResidueField ↥A) Fbar) (x' : Place (ResidueField ↥A) Fbar')
      (An An' : Annulus A (modularFunctionFieldBar N)),
    An.IsAttached C x → An'.IsAttached C' x' →
    (An'.dom = An.dom ∧ An'.modulus = An.modulus ∧
      ((An.modulus : AlgebraicClosure ℚ)) ≠ 0 ∧
      An'.param * An.param
        = algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ((An.modulus : AlgebraicClosure ℚ))) →
    ∀ (πx : AlgebraicClosure ℚ), πx ≠ 0 → (∃ hmem : πx ∈ A, (⟨πx, hmem⟩ : A) ∈ maximalIdeal A) →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) * u = πx) →
    (∃ a : AlgebraicClosure ℚ, a ∈ A ∧ (p : AlgebraicClosure ℚ) ^ k₀ = πx * a) →
    (∃ b : AlgebraicClosure ℚ, b ∈ A ∧ πx = (p : AlgebraicClosure ℚ) * b) →

    ∀ (U Uinv : Matrix (Fin r) (Fin r) (AlgebraicClosure ℚ)) (f : Fin r → modularFunctionFieldBar N),
    (∀ i j, U i j ∈ A ∧ Uinv i j ∈ A) → Uinv * U = 1 ∧ U * Uinv = 1 →
    (∀ l, f l = ∑ j, algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (U l j) * t j) →

    ∀ (w : ℕ), 2 ≤ w →
    (∃ u : AlgebraicClosure ℚ, u ∈ A ∧ u⁻¹ ∈ A ∧
      ((An.modulus : AlgebraicClosure ℚ)) = (p : AlgebraicClosure ℚ) ^ w * u) →

    (∃ hint : ∀ l : Fin r, (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
        ((p : AlgebraicClosure ℚ) ^ nexp l))⁻¹ * f l ∈ C.integers,
      (∀ l : Fin r, C.residue ⟨_, hint l⟩ ≠ 0) ∧
      (∀ l : Fin r, x.ord (C.residue ⟨_, hint l⟩) = -((nexp l / w : ℕ) : ℤ)) ∧
      LinearIndependent (ResidueField ↥A) (fun l => C.residue ⟨_, hint l⟩)) →

    (∀ i j, (p : AlgebraicClosure ℚ) ^ Bl * M i j ∈ A ∧ (p : AlgebraicClosure ℚ) ^ Bl * Minv i j ∈ A) →

    (∀ l : Fin r, ∃ h : f l ∈ C'.integers,
      C'.residue ⟨f l, h⟩ ≠ 0 ∧ (1 ≤ (l : ℕ) → 1 ≤ x'.ord (C'.residue ⟨f l, h⟩))) →
    (∃ l : Fin r, 1 ≤ (l : ℕ) ∧ ∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) →

    (∀ l : Fin r, (l : ℕ) = 0 → f l = 1) →
    (∀ R ∈ An.dom, ∀ l : Fin r, 1 ≤ (l : ℕ) →
      f l ∈ R.toValuationSubring ∧
        ∃ h : R.evalAt (f l) ∈ A, (⟨R.evalAt (f l), h⟩ : ↥A) ∈ IsLocalRing.maximalIdeal ↥A) →

    ((∃ l : Fin r, 1 ≤ (l : ℕ) ∧ (∃ h : f l ∈ C'.integers, x'.ord (C'.residue ⟨f l, h⟩) = 1) ∧ nexp l = w) ∨
     (∃ m₁ m₂ : Fin r, 1 ≤ (m₁ : ℕ) ∧ 1 ≤ (m₂ : ℕ) ∧
        (∃ h : f m₁ ∈ C'.integers, x'.ord (C'.residue ⟨f m₁, h⟩) = 1) ∧
        (∃ h : f m₂ ∈ C'.integers, x'.ord (C'.residue ⟨f m₂, h⟩) = 1) ∧
        nexp m₁ < nexp m₂ ∧ nexp m₂ < w ∧ nexp m₁ + w ≤ 2 * nexp m₂ ∧
        (∃ (h : (algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N)
              ((p : AlgebraicClosure ℚ) ^ nexp m₁))⁻¹ * f m₁ ∈ C.integers) (c : ResidueField ↥A),
          x.ord (C.residue ⟨_, h⟩ - algebraMap (ResidueField ↥A) Fbar c) = 1))) →

    (∀ μ : AbsoluteValue (AlgebraicClosure ℚ) ℝ, IsNonarchimedean μ →
      (∀ a : AlgebraicClosure ℚ, a ∈ A ↔ μ a ≤ 1) →
      ∀ P ∈ An.dom, ∀ Q ∈ An.dom, P ≠ Q →
        (∃ i j, evalVec s P i * evalVec s Q j ≠ evalVec s P j * evalVec s Q i) →
        |prox μ (evalVec s P) (evalVec s Q)
            + Real.log (μ (P.evalAt An.param - Q.evalAt An.param))|
          ≤ Cc * (-Real.log (μ ((An.modulus : AlgebraicClosure ℚ))))) := by sorry
