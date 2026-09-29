-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt
-- name    : LanglandsTunnell.TateLocal.exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/499755c0-1344-5c8e-bccc-621310a69673
-- title:
--   Fourier expansion of a Uᵥ⁽ᵇ⁾-invariant function on the local units
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and write $K_v$ for the $v$-adic completion with its valuation $\mathrm{Valued.v}$. Let $b$ be a natural number and let $g \colon K_v^\times \to \mathbb{C}$ be any function. For $n \in \mathbb{N}$ the set `higherUnitsAt K v n` consists of those units $u$ of $K_v$ with $|u|_v = 1$ and, when $n \neq 0$, also $|u - 1|_v \le \exp(-n)$; thus it is $\mathcal{O}_v^\times$ for $n = 0$ and $1 + \mathfrak{p}_v^{\,n}$ for $n \ge 1$. Assume $g(uh) = g(u)$ for every unit $u$ with $|u|_v = 1$ and every $h \in$ `higherUnitsAt K v b`. The conclusion asserts the existence of a finite set $S$ of monoid homomorphisms $\eta \colon K_v^\times \to \mathbb{C}^\times$ and of complex coefficients $c_\eta$, indexed by all such homomorphisms, such that: each $\eta \in S$ has `HasConductorExponentAt K v η m` for some $m \le b$, i.e. $\eta$ is trivial on `higherUnitsAt K v m` while for every $m' < m$ some element of `higherUnitsAt K v m'` has $\eta$-value $\neq 1$; each $\eta \in S$ is unitary, $\|\eta(x)\| = 1$ for all $x \in K_v^\times$; and $g(u) = \sum_{\eta \in S} c_\eta \, \eta(u)$ for every unit $u$ with $|u|_v = 1$.
--
--   This is the Fourier expansion, on the compact group $\mathcal{O}_v^\times$ with its finite quotient $\mathcal{O}_v^\times/(1+\mathfrak{p}_v^{\,b}) \cong (\mathcal{O}_v/\mathfrak{p}_v^{\,b})^\times$, of a function invariant under the $b$-th higher unit group, in terms of unitary characters of $K_v^\times$ of conductor exponent at most $b$; only the values on the units of valuation $1$ are controlled. It is used in the local analysis of Whittaker models and in the Rankin–Selberg step of the Langlands–Tunnell argument, where such a decomposition turns a level-one invariance property into a finite sum over characters.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_finset_hasConductorExponentAt_le_eq_sum_of_forall_mem_higherUnitsAt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (b : ℕ)
    (g : (v.adicCompletion K)ˣ → ℂ)
    (hg : ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
      ∀ h ∈ LanglandsTunnell.TateLocal.higherUnitsAt K v b, g (u * h) = g u) :
    ∃ (S : Finset ((v.adicCompletion K)ˣ →* ℂˣ)) (c : ((v.adicCompletion K)ˣ →* ℂˣ) → ℂ),
      (∀ η ∈ S, ∃ m ≤ b, LanglandsTunnell.TateLocal.HasConductorExponentAt K v η m) ∧
      (∀ η ∈ S, ∀ x : (v.adicCompletion K)ˣ, ‖((η x : ℂˣ) : ℂ)‖ = 1) ∧
      ∀ u : (v.adicCompletion K)ˣ, Valued.v (u : v.adicCompletion K) = 1 →
        g u = ∑ η ∈ S, c η * ((η u : ℂˣ) : ℂ) := by sorry
