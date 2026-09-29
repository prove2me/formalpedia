-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier
-- name    : LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/989b9261-0681-505b-9599-9e2a28e749ce
-- title:
--   Fourier transform preserves Schwartz–Bruhat functions on Kᵥ
-- statement:
--   Let $K$ be a number field and let $v$ be a point of the height-one spectrum of the ring of integers $\mathcal{O}_K$, so that $K_v$, the $v$-adic completion of $K$, is a valued field; it is equipped with a measurable space structure which is the Borel structure of its topology, and with a measure $\mu$ on $K_v$ that is an additive Haar measure. Let $\psi : K_v \to \mathbb{C}$ be an additive character and let $n \in \mathbb{Z}$ be such that, first, $\psi(x) = 1$ for every $x \in K_v$ with $\mathrm{v}(x) \le \exp(n)$ in the value group $\mathbb{Z}^{m0}$ of $K_v$, and second, there exists $x \in K_v$ with $\mathrm{v}(x) \le \exp(n+1)$ and $\psi(x) \ne 1$; thus $\psi$ is trivial on one of the balls about $0$ and nontrivial on the next larger one, i.e. it has exact level determined by $n$. Let $f : K_v \to \mathbb{C}$ be Schwartz–Bruhat, meaning that $f$ is locally constant and has compact support. The conclusion is that the function $y \mapsto \int_{K_v} f(x)\,\psi(xy)\,d\mu(x)$ is again locally constant with compact support.
--
--   This is the non-archimedean case of the statement, from the local theory of Tate's thesis, that the Fourier transform acts on the space of test functions of a local field. It is used throughout the local zeta-integral computations of this development, for instance in establishing the functional equation relating the local zeta integral of $f$ to that of its Fourier transform and in the construction of Fourier transforms attached to matrix arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_isSchwartzBruhat_tateFourier.lean

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Mathlib.RingTheory.DedekindDomain.AdicValuation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField

theorem LanglandsTunnell.TateLocal.isSchwartzBruhat_tateFourier (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure]
    (ψ : AddChar (v.adicCompletion K) ℂ) (n : ℤ)
    (hψn : ∀ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp n → ψ x = 1)
    (hψn' : ∃ x : v.adicCompletion K, Valued.v x ≤ WithZero.exp (n + 1) ∧ ψ x ≠ 1)
    (f : v.adicCompletion K → ℂ) (hf : IsSchwartzBruhat f) :
    IsSchwartzBruhat (tateFourier ψ μ f) := by sorry
