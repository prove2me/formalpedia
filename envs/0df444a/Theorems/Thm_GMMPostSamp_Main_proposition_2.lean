-- Prove2me | Theorems.Thm_GMMPostSamp_Main_proposition_2
-- name    : GMMPostSamp.Main.proposition_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:20:42.403641+00:00
-- url     : https://prove2.me/theorems/85fd628f-a79a-42c6-9e81-55fad991d663
-- title:
--   Proposition 2 — the LCV lemma: an ε-accurate estimator makes posterior draws 2ε-accurate with probability 1 − 2δ
-- statement:
--   Let $\Omega$ be a measurable space and $m:\Omega\times\Omega\to\mathbb R$ a measurable (pseudo)metric ($m(\omega,\omega)=0$, symmetric, triangle inequality), $\varepsilon>0$, $\delta\in(0,1)$ and $\pi$ a probability measure on $\Omega$. Let $\omega\sim\pi$, let $F$ be a (possibly randomized) forward operator $\Omega\to\Omega'$ (a Markov kernel) and $\varphi\sim F(\omega,\cdot)$. If a (possibly randomized) estimator $A:\Omega'\to\Omega$ satisfies $\Pr[m(A(\varphi),\omega)>\varepsilon]\le\delta$, the probability being over $\omega$, $F$ and $A$, then a draw $\hat\omega$ from the posterior $\pi(\cdot\mid\varphi)$ satisfies
--   $$\Pr\big[m(\hat\omega,\omega)>2\varepsilon\big]\le2\delta.$$
--   The posterior is any Markov kernel $\varphi\mapsto\pi(\cdot\mid\varphi)$ that disintegrates the joint law of $(\varphi,\omega)$. The statement is the localization step behind Lemma 5.
--
--   **Formalization Note.** Probabilities are measures of events under the joint laws $(\pi\otimes F)\otimes A$ and $(\pi\otimes F)\otimes\pi(\cdot\mid\cdot)$.
--
--   Differences from the source:
--   - generalization: m a metric over Ω × Ω, π ∈ P(Ω) (Ω standard Borel) → m any pseudometric (m(ω, ω) = 0, symmetric, triangle inequality) on an arbitrary measurable space Ω; reason: the proof uses only symmetry and the triangle inequality; every metric on a standard Borel space is such an m (the paper's own uses, the orbit distance of Lemma 5 and the partition Hamming distance of Proposition 6, are pseudometrics on Θ and [k]^n)
--   - reading: P[m(·, ·) > ε] → m measurable on Ω × Ω; reason: the events {m > ε} must be measurable for the probabilities to be defined
--   - encoding: randomized forward operator F, randomized estimator A, posterior π(· | φ) → Markov kernels F, A and any Markov kernel post with (π ⊗ F) swapped = (F∘π) ⊗ post; reason: a randomized map is a Markov kernel; the posterior is a regular conditional distribution, every version covered
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 11, Proposition 2 (Proposition 4 of [KSTZ25])

import Mathlib

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Proposition 2 (p. 11, the LCV lemma): let `m` be a (pseudo)metric on `Ω`, `ω ∼ π`,
`φ ∼ F(ω, ·)` observations through a randomized forward operator, and `A` a randomized
estimator with `P[m(A(φ), ω) > ε] ≤ δ`. Then a draw `ω̂` from the posterior `π(· | φ)` (any
regular version: `post` disintegrates the joint law of `(φ, ω)`) satisfies
`P[m(ω̂, ω) > 2ε] ≤ 2δ`. -/
theorem proposition_2 {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (m : Ω → Ω → ℝ) (hm : Measurable fun p : Ω × Ω => m p.1 p.2)
    (hm_self : ∀ ω, m ω ω = 0) (hm_symm : ∀ ω ω', m ω ω' = m ω' ω)
    (hm_tri : ∀ ω ω' ω'', m ω ω'' ≤ m ω ω' + m ω' ω'')
    (ε δ : ℝ) (hε : 0 < ε) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (π : Measure Ω) [IsProbabilityMeasure π] (F : Kernel Ω Ω') [IsMarkovKernel F]
    (A : Kernel Ω' Ω) [IsMarkovKernel A]
    (hA : ((π ⊗ₘ F) ⊗ₘ A.comap Prod.snd measurable_snd) {p | ε < m p.2 p.1.1} ≤
      ENNReal.ofReal δ)
    (post : Kernel Ω' Ω) [IsMarkovKernel post]
    (hpost : (π ⊗ₘ F).map Prod.swap = (F ∘ₘ π) ⊗ₘ post) :
    ((π ⊗ₘ F) ⊗ₘ post.comap Prod.snd measurable_snd) {p | 2 * ε < m p.2 p.1.1} ≤
      ENNReal.ofReal (2 * δ) := by sorry

end GMMPostSamp.Main
