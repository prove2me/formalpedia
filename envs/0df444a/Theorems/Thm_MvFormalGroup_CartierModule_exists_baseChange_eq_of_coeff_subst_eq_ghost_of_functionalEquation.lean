-- Prove2me | Theorems.Thm_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
-- name    : MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/2cf05558-1547-5ca1-a1c5-56253681d9f9
-- title:
--   Descent of a Cartier element with ghost logarithm
-- statement:
--   Fix a prime $p$ and an integer $d$, and write $A = \mathbb{Z}_p[X_{(m,i,j)}]$ and $K = \mathbb{Q}_p[X_{(m,i,j)}]$ for the polynomial rings on the index set $\mathbb{N} \times \mathrm{Fin}\,d \times \mathrm{Fin}\,d$, the map $A \to K$ being induced by $\mathbb{Z}_p \hookrightarrow \mathbb{Q}_p$. Let $\Phi_0$ be a $d$-dimensional formal group law over $A$ (a $d$-tuple of power series in two blocks of $d$ variables, with vanishing constant term, linear part $X_i + Y_i$ and associative) which is commutative. Let $a : \mathbb{N} \to M_d(K)$ and $f : \mathrm{Fin}\,d \to K[[X_1,\dots,X_d]]$ satisfy $a_0 = 1$, the functional equation $p\,a_{k+1} = \sum_{m \le k} (X_{(m,i,j)})_{i,j} \cdot \sigma^{m+1}(a_{k-m})$, where $\sigma$ is the $\mathbb{Q}_p$-algebra map $X_v \mapsto X_v^p$ applied entrywise, together with $\mathrm{coeff}_{X_j^{p^k}}(f_i) = (a_k)_{ij}$ and vanishing of all coefficients of $f_i$ at monomials not of the form $X_j^{p^k}$. Let $c : \mathbb{N} \to K^d$ satisfy $p^N c_N(j) \in A$ for all $N, j$, and $p\,c_{k+1}(j) - \sum_{m \le k}\sum_{l} X_{(m,j,l)}\,\sigma^{m+1}(c_{k-m}(l)) \in pA$ for all $k, j$. Let $m$ be an element of the Cartier module of the base change of $\Phi_0$ to $K$, that is, a $d$-tuple of power series $m_j$ in variables indexed by $\mathbb{N}$ over $K$, each with zero constant term, such that substituting the Witt addition polynomials for $p$ into $m_j$ agrees with substituting the two variable-block renamings of $m$ into the $j$-th component of the group law. Assume $\mathrm{coeff}_{X_k^{p^n}}\bigl(f_j(m)\bigr) = p^k c_{k+n}(j)$ for all $j, k, n$, and that all other coefficients of $f_j(m)$ vanish, i.e. the logarithm $f \circ m$ is the ghost combination $\sum_N c_N(j)\,w_N$. Then $m$ descends: there exists an element $m_0$ of the Cartier module of $\Phi_0$ over $A$ whose base change along $A \to K$, obtained by applying the coefficient map to each component, equals $m$.
--
--   This is the integrality, or descent, step in Hazewinkel's treatment of Cartier theory: a homomorphism from the formal group of Witt vectors to $\Phi_0$ over $K$ whose logarithm is a ghost-series combination with functional-equation integrality for the coefficients $c_N$ is already defined over $A$. It rests on the functional-equation integrality lemma [`MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation`](thm.html#MvPowerSeries.exists_map_padicInt_eq_of_subst_log_eq_of_functionalEquation), and is used in [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log) to produce the $V$-basis elements of the Cartier module of a formal group law over $A$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_CartierModule_exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_MvFormalGroup_CartierModule
import Definitions.Def_MvFormalGroup_CartierModuleHomothety
import Definitions.Def_MvFormalGroup_CartierModuleWittAction
import Definitions.Def_MvFormalGroup_CartierModuleIntVerschiebung
import Definitions.Def_MvFormalGroup_CartierModuleBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u
open MvPowerSeries in

theorem MvFormalGroup.CartierModule.exists_baseChange_eq_of_coeff_subst_eq_ghost_of_functionalEquation
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (Φ₀ : MvFormalGroup d (MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p))) [Φ₀.IsComm]
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
    (c : ℕ → Fin d → MvPolynomial (ℕ × Fin d × Fin d) (Padic p))
    (hcA : ∀ (N : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ N * c N j = MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (hcFE : ∀ (k : ℕ) (j : Fin d), ∃ r : MvPolynomial (ℕ × Fin d × Fin d) (PadicInt p),
      (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * c (k + 1) j
        - ∑ m ∈ Finset.range (k + 1), ∑ l : Fin d,
            MvPolynomial.X (m, j, l) *
              ((⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p :
                  MvPolynomial (ℕ × Fin d × Fin d) (Padic p) →ₐ[Padic p] MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))^[m + 1]) (c (k - m) l)
        = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) * MvPolynomial.map (PadicInt.Coe.ringHom (p := p)) r)
    (m : MvFormalGroup.CartierModule p
      (MvFormalGroup.map (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) Φ₀))
    (hm : ∀ (j : Fin d) (k n : ℕ),
      (coeff (Finsupp.single k (p ^ n)) (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ k * c (k + n) j)
    (hm' : ∀ (j : Fin d) (e : ℕ →₀ ℕ), (∀ k n : ℕ, e ≠ Finsupp.single k (p ^ n)) →
      (coeff e (subst m.toPowerSeries (f j)) : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) = 0) :
    ∃ m₀ : MvFormalGroup.CartierModule p Φ₀,
      MvFormalGroup.CartierModule.baseChange (MvPolynomial.map (PadicInt.Coe.ringHom (p := p))) m₀ = m := by sorry
