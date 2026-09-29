-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
-- name    : LanglandsTunnell.RankinSelberg.exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.680094+00:00
-- url     : https://prove2.me/theorems/b101b598-4b66-5c40-b148-61f558bc7e61
-- title:
--   Non-vanishing of a Hecke-local Whittaker function at a point trivial outside S_Q
-- statement:
--   Let $S_Q$ be a finite set of height-one primes of $\mathcal O_{\mathbb Q}$, with all residue rings $\mathcal O_{\mathbb Q}/\mathfrak p$ finite. Let $\varpi$ assign to each prime $\mathfrak p$ an element of the valuation ring of $\mathbb Q_{\mathfrak p}$ whose image in $\mathbb Q_{\mathfrak p}$ is non-zero and of valuation $\exp(-1)$ whenever $\mathfrak p \notin S_Q$, i.e. a uniformiser there. Let $a,b$ be complex-valued functions on primes with $b(v) \neq 0$ for $v \notin S_Q$, and let $W$ be a complex-valued function on `finiteAdelicGL2Subgroup ℚ`, the kernel of the archimedean-component homomorphism on $GL_2(\mathbb A_{\mathbb Q})$; write $g \mapsto$ [`RSCarrier.finFactor`](def/LanglandsTunnell_RSCarrierSplit.html#L17) $g$ for the map dividing an element of $GL_2(\mathbb A_{\mathbb Q})$ on the left by the image of its real archimedean $GL_2(\mathbb R)$-part. Assume four conditions for every $q \notin S_Q$ and every $g \in GL_2(\mathbb A_{\mathbb Q})$: (i) $W(\mathrm{finFactor}(\iota_q\begin{pmatrix}1&x\\0&1\end{pmatrix}\, g)) = \psi_q(x)\,W(\mathrm{finFactor}\,g)$ for all $x \in \mathbb Q_q$, where $\iota_q$ is the embedding of $GL_2(\mathbb Q_q)$ into $GL_2(\mathbb A_{\mathbb Q})$ at $q$ and $\psi_q$ is the $q$-component of the standard additive character `psiQ` of $\mathbb A_{\mathbb Q}$; (ii) $W(\mathrm{finFactor}(g\,\iota_q x)) = W(\mathrm{finFactor}\,g)$ for $x$ in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $q$ for the unit ideal, the preimage under the local embedding of the finite level-one subgroup; (iii) a Hecke recursion, $\sum_{r \in \mathcal O_{\mathbb Q}/q} W(\mathrm{finFactor}(g\,\iota_q\begin{pmatrix}\varpi_q&\beta_r\\0&1\end{pmatrix})) + W(\mathrm{finFactor}(g\,\iota_q\begin{pmatrix}1&0\\0&\varpi_q\end{pmatrix})) = a(q)\,W(\mathrm{finFactor}\,g)$, where $\beta_r$ is the image of a chosen lift of $r$; and (iv) $W(\mathrm{finFactor}(g\,\iota_q(\varpi_q I))) = (b(q)/N(q))\,W(\mathrm{finFactor}\,g)$ with $N(q)$ the absolute norm of $q$. Assume further that $W$ is right invariant under every $k$ in the finite subgroup whose $v$-component lies in [`AdelicDock.localLevelOne`](def/AdelicDock_LocalEmbedding.html#L178) at $v$ for the unit ideal for all $v \notin S_Q$ and is trivial at all $v \in S_Q$, and that $W$ is not identically zero. Then there exists $g$ in the finite subgroup with $v$-component equal to $1$ for every $v \notin S_Q$ and $W(g) \neq 0$.
--
--   This is the Hecke-locality (or "cutting") step for unramified Whittaker vectors: the local Hecke relations at the places outside $S_Q$, together with compact-open right invariance, allow the support of a non-zero Whittaker function to be moved to a point that is trivial at every place outside $S_Q$. It is used in the Rankin–Selberg part of the argument, where a non-vanishing finite translate of the relevant integrand has to be produced; the proof cites the Iwasawa decomposition over a discrete valuation ring and the level computations for the local components of the standard additive character of $\mathbb A_{\mathbb Q}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant.lean

import Definitions.Def_LanglandsTunnell_RSCarrierSplit
import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_AdelicDock_LocalEmbedding
import Definitions.Def_LanglandsTunnell_CubicInduction_Structure
import Definitions.Def_NumberField_StandardGlobalAddCharRat
import Definitions.Def_NumberField_AdelicLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField AutomorphicForm LanglandsTunnell
open NumberField.TateGlobal NumberField.AdelicLevel
open LanglandsTunnell.RankinSelberg LanglandsTunnell.CubicInduction MeasureTheory
open scoped nonZeroDivisors

theorem LanglandsTunnell.RankinSelberg.exists_forall_localAt_eq_one_and_ne_zero_of_heckeLocal_of_levelOne_invariant
    (SQ : Finset (HeightOneSpectrum (𝓞 ℚ)))
    [hIfin : ∀ p : HeightOneSpectrum (𝓞 ℚ), Fintype (𝓞 ℚ ⧸ p.asIdeal)]
    (ϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p.adicCompletionIntegers ℚ)
    (hπ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p) ≠ 0)
    (hϖ : ∀ p : HeightOneSpectrum (𝓞 ℚ), p ∉ SQ →
      Valued.v (algebraMap (p.adicCompletionIntegers ℚ) (p.adicCompletion ℚ) (ϖ p)) = WithZero.exp (-1 : ℤ))
    (aev bev : HeightOneSpectrum (𝓞 ℚ) → ℂ) (hbev : ∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → bev v ≠ 0)
    (W : finiteAdelicGL2Subgroup ℚ → ℂ)

    (hHL :         (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ → ∀ (x : q.adicCompletion ℚ) (g : AdelicGL2 (𝓞 ℚ) ℚ),
          W (RSCarrier.finFactor (UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.unipotent x) * g)) =
            psiLoc NumberField.StandardAddChar.psiQ q x * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), q ∉ SQ →
          ∀ (x : GL (Fin 2) (q.adicCompletion ℚ)) (g : AdelicGL2 (𝓞 ℚ) ℚ),
            x ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ q ⊤ →
              W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q x)) = W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          (∑ r, W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repSome
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ)
                (algebraMap (𝓞 ℚ) (q.adicCompletionIntegers ℚ) (Quotient.out (r : 𝓞 ℚ ⧸ q.asIdeal)))))))) +
            W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.repInf
              (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            aev q * W (RSCarrier.finFactor g)) ∧
        (∀ q : HeightOneSpectrum (𝓞 ℚ), ∀ hq : q ∉ SQ, ∀ g : AdelicGL2 (𝓞 ℚ) ℚ,
          W (RSCarrier.finFactor (g * UnramifiedWhittaker.placeEmbed ℚ q (UnramifiedWhittaker.scalarPi
            (algebraMap (q.adicCompletionIntegers ℚ) (q.adicCompletion ℚ) (ϖ q)) (hπ q hq)))) =
            (bev q / (Ideal.absNorm q.asIdeal : ℂ)) * W (RSCarrier.finFactor g)))

    (hK : ∀ k : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ →
        localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ v ⊤) →
      (∀ v ∈ SQ, localAt ℚ v (k : AdelicGL2 (𝓞 ℚ) ℚ) = 1) →
      ∀ g : finiteAdelicGL2Subgroup ℚ, W (g * k) = W g)
    (hne : ∃ g : finiteAdelicGL2Subgroup ℚ, W g ≠ 0) :
    ∃ g : finiteAdelicGL2Subgroup ℚ,
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ SQ → localAt ℚ v (g : AdelicGL2 (𝓞 ℚ) ℚ) = 1) ∧ W g ≠ 0 := by sorry
