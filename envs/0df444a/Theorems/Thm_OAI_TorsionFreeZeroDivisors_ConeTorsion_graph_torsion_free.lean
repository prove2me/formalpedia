-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_ConeTorsion_graph_torsion_free
-- name    : OAI.TorsionFreeZeroDivisors.ConeTorsion.graph_torsion_free
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:11:53.785676+00:00
-- url     : https://prove2.me/theorems/140fbb01-5b30-4eca-9861-508c82cf734d
-- title:
--   Corollary 5.3 (OpenAI) — a coned graph presentation without reduced spherical pictures is torsion-free
-- statement:
--   Let $\Gamma$ be a port graph with vertex set $V$ and dart set $D$: an origin map $o:D\to V$ and a fixed-point-free involution $d\mapsto\bar d$ (the reverse dart), with terminus $t(d)=o(\bar d)$. Let $\lambda:D\to S\times\{\pm\}$ label each dart by a generator and a sign, with $\lambda(\bar d)=\lambda(d)^*$, where $(s,\pm)^*=(s,\mp)$. Let $R$ be a choice of routes: a base-point map $\beta:V\to V$, constant along darts and idempotent ($\beta(\beta(v))=\beta(v)$), and for each vertex $v$ a path $\pi_v$ from $\beta(v)$ to $v$. Write $w(v)\in F(S)$ for the label of $\pi_v$. Let $G$ be the group
--
--   $$G=\big\langle\,S\ \big|\ w(o(d))\,\ell(d)\,w(t(d))^{-1}\ (d\in D)\,\big\rangle ,$$
--
--   where $\ell(d)=s^{\pm1}$ is the letter of $\lambda(d)$. In it every closed path in $\Gamma$ has trivial label: this is the group of $\Gamma$ coned off along its labelled map to the rose on $S$.
--
--   Assume that no spherical picture over $(\Gamma,\lambda)$ is reduced. A spherical picture is a finite nonempty set $P$ with a rotation $\sigma$, a fixed-point-free involution $\alpha$ pairing positions with the same generator and opposite signs, and darts $\delta:P\to D$ that form closed paths along the cycles of $\sigma$. The pair $(\sigma,\alpha)$ satisfies the genus-zero equation $2c(\sigma)+2c(\alpha\sigma)=|P|+4k(\sigma,\alpha)$, where $c$ counts cycles and $k$ counts orbits of $\langle\sigma,\alpha\rangle$. A picture is reduced if $\delta(\alpha(i))\neq\overline{\delta(i)}$ and $\delta(\sigma(i))\neq\overline{\delta(i)}$ for every $i$. Then $G$ is torsion-free:
--
--   $$g\in G,\ n>0,\ g^n=1\ \Longrightarrow\ g=1 .$$
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 23: “Corollary 5.3. The universal cover of $X$ is contractible, and $G$ is torsion-free.” In the paper, Proposition 5.1 (“The complex $X$ satisfies $\pi_2(X) = 0$.”) is proved by turning a minimal sphere picture into a reduced spherical arrangement, which Proposition 4.5 excludes. This statement is the torsion-free half of Corollary 5.3, for an arbitrary coned graph presentation, with the absence of reduced pictures as its hypothesis. The construction applies it to the sampled graphs through `OAI.TorsionFreeZeroDivisors.SampleGraph.SpherePicture.excluded`.
--
--   **Formalization note.** The objects are OpenAI's: `PortSubdivision.PortGraph`, `GraphPresentation.Routes`, `GraphPresentation.Group` (a Mathlib `PresentedGroup`, with $\ell$ given by `ConeSigned.freeLetter`), `SphericalPicture.Data` and `Data.Reduced`, all from the bundle `Def_TorsionFreeZeroDivisorsConstruction`. No finiteness of $V$, $D$ or $S$ is assumed. Torsion-freeness is stated as $g^n=1,\ n>0\Rightarrow g=1$.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, pp. 20-23, Proposition 5.1 and Corollary 5.3 (torsion-freeness), for a general coned graph presentation without reduced spherical pictures; Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), ConeTorsion.graph_torsion_free

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.ConeTorsion

open scoped Classical
open PortSubdivision GraphPresentation

theorem graph_torsion_free {V D S : Type} (Γ : PortGraph V D) (R : Routes Γ) (label : D→S×Bool)
    (hl : ∀d,label (Γ.reverse d)=WordPairing.inverseLetter (label d))
    (hbase : ∀v,R.base (R.base v)=R.base v)
    (hex : ∀{P : Type}[Fintype P][Nonempty P]
      (a : SphericalPicture.Data (O:=P) Γ label WordPairing.inverseLetter),¬a.Reduced) :
    ∀ (g : GraphPresentation.Group Γ (ConeSigned.freeLetter ∘ label) R) (n : ℕ),
      0 < n → g ^ n = 1 → g = 1 := by
  sorry

end OAI.TorsionFreeZeroDivisors.ConeTorsion
