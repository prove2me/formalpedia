-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat
-- name    : LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:10.196979+00:00
-- url     : https://prove2.me/theorems/dfe5cd4a-7523-5ca2-bf52-535caf1fe5c3
-- title:
--   Fourier inversion at v for the self-dual measure
-- statement:
--   Let $K$ be a number field and $v$ a finite place of $K$, i.e. a height-one prime of $\mathcal{O}_K$, and let $K_v$ denote the associated adic completion, equipped with its valuation $\mathrm{v}$ taking values in $\{0\}\cup\exp(\mathbb{Z})$ and with its Borel $\sigma$-algebra. Let $\psi_{K,v}$ be the additive character of $K_v$ obtained by composing the standard additive character of the adele ring of $K$ with the additive map sending $x\in K_v$ to the adele which is $x$ at $v$ and $0$ elsewhere, let $n$ be its level, defined as the supremum of the set of integers $m$ such that $\psi_{K,v}$ is trivial on $\{x : \mathrm{v}(x)\le \exp m\}$, and let $\mu$ be the Haar measure on $K_v$ given by $(N v)^{-n/2}$ times the additive Haar measure normalising the valuation ring $\mathcal{O}_v$ to have measure $1$, where $Nv$ is the absolute norm of the prime ideal $v$. For $g : K_v\to\mathbb{C}$ write $\hat g(y)=\int g(x)\,\psi_{K,v}(xy)\,d\mu(x)$. Then for every $f : K_v\to\mathbb{C}$ which is locally constant and has compact support, and every $x\in K_v$, one has $\hat{\hat f}(x)=f(-x)$.
--
--   This is the Fourier inversion formula at a finite place in the standard normalisation, expressing that the measure $\mu$ with $\mu(\mathcal{O}_v)=(Nv)^{-n/2}$ is self-dual for the character $\psi_{K,v}$ of level $n$, so that local functional equations computed with $\mu$ carry no extra volume constant. It is used in the local Tate-integral computations of the Langlands–Tunnell part of the development, notably in the treatment of local zeta integrals and their functional equations and in the cubic-induction Fourier identities.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat.lean

import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.StandardAddChar

theorem LanglandsTunnell.TateLocal.tateFourier_tateFourier_selfDualHaarAt_of_isSchwartzBruhat (K : Type)
    [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (f : v.adicCompletion K → ℂ)
    (hf : IsSchwartzBruhat f) (x : v.adicCompletion K) :
    letI := localBorel K v
    tateFourier (psiLocal K v) (selfDualHaarAt K v) (tateFourier (psiLocal K v) (selfDualHaarAt K v) f) x
      = f (-x) := by sorry
