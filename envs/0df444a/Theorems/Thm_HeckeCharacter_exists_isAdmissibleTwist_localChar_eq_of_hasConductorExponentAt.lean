-- Prove2me | Theorems.Thm_HeckeCharacter_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
-- name    : HeckeCharacter.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/84ae55b1-6529-5a87-9f4b-d7b086c30456
-- title:
--   Admissible Hecke character of ℚ with prescribed local components
-- statement:
--   Let $S$ be a finite set of finite places of $\mathbb{Q}$ (height one primes of $\mathcal{O}_{\mathbb{Q}}$), let $\xi$ assign to each finite place $v$ a monoid homomorphism $\xi_v \colon (\mathbb{Q}_v)^{\times} \to \mathbb{C}^{\times}$, and let $n \colon v \mapsto n_v$ be a function to $\mathbb{N}$. Assume that for every $v \in S$ the character $\xi_v$ has conductor exponent exactly $n_v$, in the sense of `HasConductorExponentAt`: $\xi_v$ is trivial on the set of units $u$ with $|u|_v = 1$ and (if $n_v > 0$) $|u - 1|_v \le q_v^{-n_v}$, and for every $m < n_v$ there is a unit $u$ in the corresponding set at level $m$ with $\xi_v(u) \neq 1$. Then there is a monoid homomorphism $\tau$ from the idele group $(\mathbb{A}_{\mathbb{Q}})^{\times}$ to $\mathbb{C}^{\times}$ which is an admissible twist, i.e. trivial on the principal ideles $\mathbb{Q}^{\times}$, continuous, and of absolute value $1$ everywhere, and such that: (i) for each $v \in S$ and each $u \in (\mathbb{Q}_v)^{\times}$ with both $u$ and $u^{-1}$ in the valuation ring, the local component `localChar` $\tau$ at $v$ — that is, $\tau$ evaluated on the idele with entry $u$ at $v$ and $1$ elsewhere — equals $\xi_v(u)$; (ii) for each $v \in S$ that local component has conductor exponent exactly $n_v$ in the same sense; (iii) for each finite $v \notin S$ the local component of $\tau$ is trivial on all such $u$; and (iv) there is an integer $e$ such that at every real place $w$ of $\mathbb{Q}$ the archimedean component of $\tau$ is $x \mapsto (\iota_w(x)/\|x\|)^e$, the absolute-value exponent being $0$.
--
--   This is the existence statement for Hecke (Größen-) characters of $\mathbb{Q}$ with prescribed unit components at finitely many primes, exact conductor exponents there, unramified behaviour elsewhere, and a pure sign type at the real place. It supplies the auxiliary twisting characters used in the cubic-induction and converse-theorem steps of the Langlands–Tunnell input, where a fixed automorphic object must be twisted so that its local components match prescribed ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeCharacter_exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain NumberField.TateGlobal LanglandsTunnell.TateLocal LanglandsTunnell.Converse

theorem HeckeCharacter.exists_isAdmissibleTwist_localChar_eq_of_hasConductorExponentAt
    (S : Finset (HeightOneSpectrum (𝓞 ℚ)))
    (ξ : (v : HeightOneSpectrum (𝓞 ℚ)) → (v.adicCompletion ℚ)ˣ →* ℂˣ) (n : HeightOneSpectrum (𝓞 ℚ) → ℕ)
    (hξ : ∀ v ∈ S, HasConductorExponentAt ℚ v (ξ v) (n v)) :
    ∃ τ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ,
      IsAdmissibleTwist ℚ τ ∧
      (∀ v ∈ S, ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
        ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
          localChar τ v u = ξ v u) ∧
      (∀ v ∈ S, HasConductorExponentAt ℚ v (localChar τ v) (n v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → IsUnramifiedCharAt τ v) ∧
      ∃ e : ℤ, ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ τ w 0 e := by sorry
