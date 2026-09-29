-- Prove2me | Theorems.Thm_KServer_lazyPot_ge_instance
-- name    : KServer.lazyPot_ge_instance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T16:27:57.627945+00:00
-- url     : https://prove2.me/theorems/d052e050-a5ae-4b3b-a2d2-e40fd1e3e687
-- title:
--   Instantiating the lazy potential at arbitrary witnesses
-- statement:
--   The lazy potential $\Psi_{w,r} = \hat w(r) + \dot w(r)$ is a supremum, so every choice of witnesses gives a lower bound. Written out with all three of its nested suprema instantiated, that bound reads
--
--   $$\Psi_{w,r}\;\ge\;\bigl(ra + ra' - w(r,a,a')\bigr) + \bigl(pb + pb' - w(r,b,b')\bigr)
--   + \bigl(dd' - w(r,p,d) - w(r,p,d')\bigr)$$
--
--   for **all** points $a, a', p, b, b', d, d'$.
--
--   ## Role
--
--   This is the tool with which the twelve-case analysis of the update property is discharged. Each case takes the expansion of $\Psi_{w,s}$ at an arbitrary set of witnesses, substitutes the branch of the update formula that realises each of its three work-function values, rearranges using the triangle inequality and quasiconvexity, and arrives at an expression of exactly the shape displayed above — at which point this lemma identifies it as a lower bound for $\Psi_{w,r}$ and the case is closed. Ten of the twelve cases end this way (two of them at an *average* of two such instances, which is equally covered since the bound is linear); the remaining two land on the auxiliary potentials $\Lambda$ and $\Gamma$ instead.
--
--   Note the three groups of terms correspond to the three suprema: $(a,a')$ instantiates the shadow $\hat w(r)$, using $d(r,r) = 0$; $(b,b')$ instantiates the inner two-point shadow $\tilde w(r,p)$; and $(p,d,d')$ instantiates $\dot w(r)$. The witnesses are completely free — in particular no distinctness and no minimality is assumed of any of them, which is what makes the lemma usable at whatever configuration a case analysis happens to produce.
--
--   **Formalization note.** Each instantiation is `le_csSup`, which needs the corresponding set to be bounded above; all three bounds come from the unit-rate growth of the work function taken with base point $r$.
-- source:
--   W. Bein, M. Chrobak, L. Larmore, The 3-Server Problem in the Plane, Theoretical Computer Science 289(1) (2002) 335-354, Section 3: the definition of Psi via the shadow and dotW, used in this instantiated form throughout the twelve cases of Lemma 4 ('we obtained an expression that is an instance of Psi_{w,r} for some choice of parameters').

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_lazy_potential

namespace KServer

theorem lazyPot_ge_instance (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (r a a' p b b' d d' : M) :
    (dist r a + dist r a' - workFnU C₀ σ ![r, a, a'])
      + ((dist p b + dist p b' - workFnU C₀ σ ![r, b, b'])
          + (dist d d' - workFnU C₀ σ ![r, p, d] - workFnU C₀ σ ![r, p, d']))
      ≤ lazyPot C₀ σ r := by sorry

end KServer
