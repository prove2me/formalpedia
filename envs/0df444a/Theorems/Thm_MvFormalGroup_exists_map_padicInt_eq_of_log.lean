-- Prove2me | Theorems.Thm_MvFormalGroup_exists_map_padicInt_eq_of_log
-- name    : MvFormalGroup.exists_map_padicInt_eq_of_log
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/de99f37d-eb76-55da-b527-fe315a0aaf7f
-- title:
--   Functional-equation integrality for the universal p-typical law
-- statement:
--   Fix a prime $p$, a dimension $d$, and let $A_{\mathbb{Q}_p} = \mathbb{Q}_p[V_{m,i,j}]$ be the polynomial ring over the $p$-adic field `Padic p` on variables indexed by $(m,i,j) \in \mathbb{N} \times \mathrm{Fin}\,d \times \mathrm{Fin}\,d$. Let $\Phi$ be a $d$-dimensional formal group law over $A_{\mathbb{Q}_p}$, that is, $d$ power series in the $2d$ variables indexed by $\mathrm{Fin}\,d \oplus \mathrm{Fin}\,d$ with vanishing constant term, whose coefficients at the degree-one monomials in either block of variables are $\delta_{ij}$, and which satisfy the associativity identity. Let $a : \mathbb{N} \to M_d(A_{\mathbb{Q}_p})$ and $f : \mathrm{Fin}\,d \to A_{\mathbb{Q}_p}[[X_1,\dots,X_d]]$ be subject to: $a_0$ is the identity matrix; for every $k$, $p \cdot a_{k+1} = \sum_{m=0}^{k} V_m \cdot \sigma^{m+1}(a_{k-m})$, where $V_m$ is the matrix with entries the variables $X_{(m,i,j)}$ and $\sigma$ is the entrywise $\mathbb{Q}_p$-algebra endomorphism sending each variable $X_v$ to $X_v^p$, applied $m+1$ times; the coefficient of $f_i$ at the monomial $X_j^{p^k}$ is $(a_k)_{ij}$ for all $i,j,k$; all coefficients of $f_i$ at exponent vectors not of the form $\mathrm{single}\,j\,(p^k)$ vanish; and $f$ is a logarithm for $\Phi$, in the sense that for each $i$ the substitution of the family $\Phi$ into $f_i$ equals the sum of $f_i$ in the first block of variables and $f_i$ in the second block. The conclusion is that there is a $d$-dimensional formal group law $\Phi_0$ over $\mathbb{Z}_p[V_{m,i,j}]$ whose coefficientwise image under the map induced by the inclusion $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$ is $\Phi$.
--
--   This is Hazewinkel's functional-equation (integrality) lemma, specialised to the universal $p$-typical situation: a formal group law over the rational polynomial ring whose logarithm is supported on the $p$-power monomials and satisfies the $V$-recursion already has $p$-integral coefficients. It is used in the construction of a Cartier module with a $V$-basis over $\mathbb{Z}_p[V_{m,i,j}]$, via [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_exists_map_padicInt_eq_of_log.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.exists_map_padicInt_eq_of_log
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (f : Fin d → MvPowerSeries (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (h3 : ∀ (i j : Fin d) (k : ℕ), ((f i).coeff (Finsupp.single j (p ^ k)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = a k i j)
    (h4 : ∀ (i : Fin d) (e : Fin d →₀ ℕ),
      (∀ (j : Fin d) (k : ℕ), e ≠ Finsupp.single j (p ^ k)) → ((f i).coeff e : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0)
    (h5 : ∀ i : Fin d,
      MvPowerSeries.subst Φ.toPowerSeries (f i)
        = MvPowerSeries.subst (fun j => (MvPowerSeries.X (Sum.inl j) : MvPowerSeries (Fin d ⊕ Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))) (f i)
          + MvPowerSeries.subst (fun j => MvPowerSeries.X (Sum.inr j)) (f i)) :
    ∃ Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p)),
      MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀ = Φ := by sorry
